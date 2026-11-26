"""Rebuild, inspect every declaration, and replay each proof module separately.

Run from the project root with: python verification/replay.py
Use --fresh-imports for an additional replay including imported declarations.
A new checkout without a .lake/build directory gives a fresh source build.
The verifier aborts on any failed subprocess, uncovered object name or new axiom.
"""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "verification"


def run(args, log=None, cwd=ROOT):
    result = subprocess.run(args, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output = result.stdout.decode("utf-8", "replace")
    if log:
        (REPORT / log).write_text("$ " + " ".join(map(str, args)) + "\n" + output,
                                  encoding="utf-8")
    if result.returncode:
        raise RuntimeError(f"{args[0]} exited with {result.returncode}\n{output[-6000:]}")
    return output


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def modules():
    files = [ROOT / "ManuscriptProofs.lean", *sorted((ROOT / "ManuscriptProofs").rglob("*.lean"))]
    return {".".join(p.relative_to(ROOT).with_suffix("").parts): p for p in files}


def source_audit(sources):
    # Strip nested Lean comments, line comments, and string literals before
    # scanning. Every manuscript source is also included for human inspection.
    outer = re.compile(r"/-|--[^\n]*|\"(?:\\.|[^\"\\])*\"")
    inner = re.compile(r"/-|-/")
    forbidden = re.compile(r"\b(?:axiom|opaque|unsafe|partial|sorryAx|sorry|admit|native_decide|"
                           r"ofReduceBool|ofReduceNat|_unsafe_rec|implemented_by|extern|trustCompiler|"
                           r"run_cmd|run_tac|initialize|builtin_initialize|elab_rules|elab|macro_rules|"
                           r"setEnv|addDecl|addAndCompile)\b")
    edges = {}
    for name, path in sources.items():
        body = path.read_text(encoding="utf-8-sig")
        depth = last = 0
        code = []
        while match := (inner if depth else outer).search(body, last):
            if not depth:
                code.append(body[last:match.start()])
            token = match.group()
            if token == "/-":
                depth += 1
            elif token == "-/":
                depth -= 1
            code.append(" ")
            last = match.end()
        if depth:
            raise ValueError(f"unbalanced comment in {name}")
        text = "".join(code) + body[last:]
        bad = forbidden.search(text)
        if bad:
            raise ValueError(f"{name}: review restricted source token {bad.group()}")
        edges[name] = re.findall(r"(?m)^\s*import\s+(ManuscriptProofs[\w.]*)", text)
    seen = set()

    def visit(name, stack):
        if name in stack:
            raise ValueError(f"import cycle through {name}")
        if name not in seen:
            for child in edges[name]:
                visit(child, stack | {name})
            seen.add(name)
    visit("ManuscriptProofs", set())
    if seen != set(sources):
        raise ValueError(f"unreachable source modules: {set(sources) - seen}")
    lines = [f"{name}\t{digest(sources[name])}\t{','.join(edges[name])}" for name in sources]
    (REPORT / "source-imports.tsv").write_text("module\tsha256\tproject imports\n" +
                                              "\n".join(lines) + "\n", encoding="utf-8")


def dependencies():
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8-sig"))
    lines = ["Git HEAD, normalized tracked diff and full porcelain status checked for each dependency."]
    for package in manifest["packages"]:
        path = (ROOT / manifest["packagesDir"] / package["name"]).resolve()
        args = ["git", "-c", f"safe.directory={path.as_posix()}", "-c", "core.autocrlf=true",
                "-C", str(path)]
        head = run(args + ["rev-parse", "HEAD"]).strip()
        status = run(args + ["status", "--porcelain", "--untracked-files=normal"]).strip()
        run(args + ["diff", "--quiet", "--ignore-cr-at-eol", "HEAD", "--"])
        if head != package["rev"] or status:
            raise ValueError(f"{package['name']}: pin or clean-tree mismatch: {head} {status}")
        lines.append(f"{package['name']} {head} clean")
    (REPORT / "dependencies.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")


def audit(fresh):
    sources = modules()
    source_audit(sources)
    deps_started = time.monotonic()
    dependencies()
    print(f"Verified {len(sources)} source modules and dependency pins "
          f"in {time.monotonic()-deps_started:.1f}s", flush=True)
    run(["lean", "Audit.lean"], "axioms.txt")
    run(["lean", "verification/Interfaces.lean"], "interfaces.txt")
    inv = run(["lean", "verification/Inventory.lean"], "inventory.tsv")
    objs = run(["lean", "--run", "verification/ObjectNames.lean", *sources], "object-names.tsv")
    rows = [line.split("\t") for line in inv.splitlines() if line.startswith("DECL\t")]
    runtime = {tuple(line.split("\t")[1:3]) for line in inv.splitlines() if line.startswith("RUNTIME\t")}
    expected = {tuple(line.split("\t")[1:]) for line in objs.splitlines() if line.startswith("OBJ\t")}
    counts = {p[1]: int(p[2]) for l in objs.splitlines() if (p := l.split("\t"))[0] == "MOD"}
    for line in objs.splitlines():
        fields = line.split("\t")
        if fields[0] == "MOD":
            binary = ROOT / ".lake/build/lib/lean" / Path(*fields[1].split(".")).with_suffix(".olean")
            if Path(fields[3]).resolve() != binary.resolve():
                raise ValueError(f"{fields[1]} was imported from another checkout: {fields[3]}")
    actual = {(module, name) for _, module, name, _, _ in rows}
    if set(counts) != set(sources) or len(rows) != len(actual) or expected != actual:
        raise ValueError(f"object coverage mismatch: missing {sorted(expected-actual)[:12]}, "
                         f"extra {sorted(actual-expected)[:12]}")
    if counts["ManuscriptProofs"] != 0:
        raise ValueError("entry point gained declarations; replay its exact object separately")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if any(set(filter(None, aks.split(","))) - allowed for _, _, _, _, aks in rows):
        raise ValueError("unexpected transitive axiom")
    lean = Path(shutil.which("lean")).resolve()
    checker = Path(shutil.which("leanchecker")).resolve()
    prefix = Path(run(["lean", "--print-prefix"]).strip())
    binary = prefix / "bin"
    artifacts = [binary / lean.name, binary / checker.name]
    artifacts += list(binary.glob("libleanshared*.dll"))
    lines = [run(["lean", "--version"]).strip(), "Toolchain artifact SHA-256"]
    lines += [f"{p.name}\t{digest(p)}" for p in artifacts]
    (REPORT / "toolchain.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
    kernels = REPORT / "kernel-replay.tsv"
    with kernels.open("w", encoding="utf-8") as results:
        results.write("module\tobject declarations\tresult\telapsed seconds\tcommand output\n")
        for name in sorted(sources):
            if name == "ManuscriptProofs":
                results.write(f"{name}\t0\tPASS\t0\tFresh-imported entry point with zero declarations\n")
                continue
            if any(other.startswith(name + ".") for other in sources):
                raise ValueError(f"{name} would select multiple object files")
            start = time.monotonic()
            output = run(["leanchecker", "--verbose", name]).strip()
            if output != f"replaying {name}":
                raise ValueError(f"unexpected checker coverage for {name}: {output}")
            elapsed = time.monotonic() - start
            results.write(f"{name}\t{counts[name]}\tPASS\t{elapsed:.2f}\t{output}\n")
            results.flush()
            print(f"Kernel replay passed {name} ({counts[name]} declarations)", flush=True)
    print("Replaying the union of the actual mathematical dependency closures", flush=True)
    closure = run(["lean", "verification/Closure.lean"], "kernel-closure.txt")
    root_counts = re.search(r"Local object declarations: (\d+); total logical roots: (\d+); "
                            r"generated partial runtime helpers excluded and unreachable: (\d+)", closure)
    if not root_counts or tuple(map(int, root_counts.groups())) != (
            len(rows), len(rows)-len(runtime), len(runtime)) or not runtime <= actual:
        raise ValueError("logical roots and runtime helpers disagree between the two audits")
    if fresh:
        print("Starting extra empty-environment replay of the full dependency closure", flush=True)
        run(["leanchecker", "--fresh", "--verbose", "ManuscriptProofs"], "fresh-imports.txt")
    print(f"Verified {len(rows)} declarations; kinds {dict(Counter(row[3] for row in rows))}",
          flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--in-lake", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--fresh-imports", action="store_true")
    options = parser.parse_args()
    if options.in_lake:
        audit(options.fresh_imports)
        return
    os.environ.setdefault("LEAN_NUM_THREADS", "2")
    os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
    run(["lake", "build"], "build.txt")
    args = ["lake", "env", sys.executable, str(Path(__file__).resolve()), "--in-lake"]
    if options.fresh_imports:
        args.append("--fresh-imports")
    subprocess.run(args, cwd=ROOT, check=True)


if __name__ == "__main__":
    main()
