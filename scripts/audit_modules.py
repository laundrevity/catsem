#!/usr/bin/env python3
import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile

ALLOWED = {"propext", "Quot.sound"}
PROJECT_PREFIXES = ("Specs/", "Proofs/")
PROJECT_MOD_PREFIXES = ("Specs.", "Proofs.")


def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def is_valid_mod_name(mod: str) -> bool:
    return bool(mod) and all(part.isidentifier() for part in mod.split("."))


def get_lean_path_dirs() -> list[str]:
    proc = subprocess.run(
        ["lake", "env", "printenv", "LEAN_PATH"],
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        print("❌ FAIL: Could not query LEAN_PATH via `lake env printenv LEAN_PATH`.", file=sys.stderr)
        sys.stderr.write(proc.stderr)
        sys.exit(1)
    raw = proc.stdout.strip()
    if not raw:
        return []
    return [p for p in raw.split(os.pathsep) if p]


def check_no_ambiguous_project_oleans() -> dict[str, str]:
    """Scan both .lake/build and all LEAN_PATH roots for project .olean files.
    Fails closed if any Specs/* or Proofs/* .olean exists at multiple distinct realpaths.
    Returns mapping 'Specs.Defs' -> canonical realpath for discovered project .olean files.
    """
    found: dict[str, set[str]] = {}

    # 1. Scan every directory in LEAN_PATH for Specs/*.olean and Proofs/*.olean
    for entry in get_lean_path_dirs():
        if not os.path.isdir(entry):
            continue
        for prefix_dir in ("Specs", "Proofs"):
            sub = os.path.join(entry, prefix_dir)
            if not os.path.isdir(sub):
                continue
            for root, _, files in os.walk(sub):
                for fn in files:
                    if fn.endswith(".olean"):
                        full = os.path.realpath(os.path.join(root, fn))
                        rel = os.path.relpath(os.path.join(root, fn), entry).replace(os.sep, "/")
                        mod = rel[:-6].replace("/", ".")
                        found.setdefault(mod, set()).add(full)

    # 2. Scan the entire .lake/build tree for any stray/decoy */Specs/*.olean or */Proofs/*.olean
    build_root = os.path.join(".lake", "build")
    if os.path.isdir(build_root):
        for root, _, files in os.walk(build_root):
            for fn in files:
                if not fn.endswith(".olean"):
                    continue
                rel_from_build = os.path.relpath(os.path.join(root, fn), build_root).replace(os.sep, "/")
                parts = rel_from_build.split("/")
                for idx, part in enumerate(parts[:-1]):
                    if part in ("Specs", "Proofs"):
                        mod_rel = "/".join(parts[idx:])
                        mod = mod_rel[:-6].replace("/", ".")
                        full = os.path.realpath(os.path.join(root, fn))
                        found.setdefault(mod, set()).add(full)
                        break

    ambiguous = {mod: sorted(paths) for mod, paths in found.items() if len(paths) > 1}
    if ambiguous:
        for mod, paths in sorted(ambiguous.items()):
            print(f"❌ FAIL: Ambiguous .olean artifacts detected for '{mod}': {paths}", file=sys.stderr)
        sys.exit(1)

    return {mod: next(iter(paths)) for mod, paths in found.items() if len(paths) == 1}


def resolve_oleans_via_lean(mods: list[str]) -> dict[str, str]:
    """Use Lean.findOLean inside `lake env lean --run` to resolve exact module .olean paths."""
    for m in mods:
        if not is_valid_mod_name(m):
            print(f"❌ FAIL: Invalid module identifier '{m}'.", file=sys.stderr)
            sys.exit(1)

    mod_lits = ", ".join(f"`{m}" for m in mods)
    with tempfile.TemporaryDirectory(prefix="catsem_resolve_olean_") as tmpdir:
        driver = os.path.join(tmpdir, "ResolveOLean.lean")
        report = os.path.join(tmpdir, "resolved.tsv")
        report_lit = json.dumps(report)
        lean_src = f"""import Lean

def main : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let mods : Array Lean.Name := #[{mod_lits}]
  let mut out : Array String := #[]
  for m in mods do
    let p ← Lean.findOLean m
    let rp ← IO.FS.realPath p
    out := out.push s!"{{m}}\\t{{rp}}"
  IO.FS.writeFile (System.FilePath.mk {report_lit}) (String.intercalate "\\n" out.toList ++ "\\n")
  return 0
"""
        with open(driver, "w", encoding="utf-8") as f:
            f.write(lean_src)
        proc = subprocess.run(
            ["lake", "env", "lean", "--run", driver],
            capture_output=True,
            text=True,
        )
        if proc.returncode != 0 or not os.path.exists(report):
            sys.stderr.write(proc.stdout)
            sys.stderr.write(proc.stderr)
            print(f"❌ FAIL: Lean.findOLean failed for {mods}.", file=sys.stderr)
            sys.exit(1)

        resolved: dict[str, str] = {}
        with open(report, "r", encoding="utf-8") as rf:
            for line in rf:
                s = line.rstrip("\r\n")
                if not s:
                    continue
                parts = s.split("\t")
                if len(parts) != 2:
                    print(f"❌ FAIL: Malformed ResolveOLean line: {s}", file=sys.stderr)
                    sys.exit(1)
                resolved[parts[0]] = os.path.realpath(parts[1])

    for m in mods:
        if m not in resolved or not os.path.isfile(resolved[m]):
            print(f"❌ FAIL: Lean.findOLean did not resolve an existing file for '{m}'.", file=sys.stderr)
            sys.exit(1)
    return resolved


def parse_binding_spec(spec: str, flag_name: str) -> tuple[str, str, str]:
    """Parse MOD=PATH:SHA256."""
    if "=" not in spec or ":" not in spec.split("=", 1)[1]:
        print(f"❌ FAIL: Invalid {flag_name} '{spec}' (expected MOD=PATH:SHA256).", file=sys.stderr)
        sys.exit(1)
    mod, rest = spec.split("=", 1)
    path_part, sha_part = rest.rsplit(":", 1)
    mod = mod.strip()
    path_part = path_part.strip()
    sha_part = sha_part.strip().lower()
    if not is_valid_mod_name(mod) or not path_part or len(sha_part) != 64:
        print(f"❌ FAIL: Malformed {flag_name} '{spec}'.", file=sys.stderr)
        sys.exit(1)
    return mod, path_part, sha_part


def verify_olean_bindings(bindings: dict[str, tuple[str, str]], discovered: dict[str, str]) -> dict[str, tuple[str, str]]:
    """Verify every module in bindings resolves via Lean.findOLean to expected realpath and SHA-256."""
    if not bindings:
        return {}
    mods = list(bindings.keys())
    resolved = resolve_oleans_via_lean(mods)
    verified: dict[str, tuple[str, str]] = {}
    for mod, (exp_path, exp_sha) in bindings.items():
        exp_real = os.path.realpath(exp_path)
        res_real = resolved[mod]
        if res_real != exp_real:
            print(
                f"❌ FAIL: Artifact binding path mismatch for '{mod}': "
                f"expected '{exp_real}', but Lean.findOLean resolved '{res_real}'.",
                file=sys.stderr,
            )
            sys.exit(1)
        if mod in discovered and discovered[mod] != res_real:
            print(
                f"❌ FAIL: Search-path mismatch for '{mod}': "
                f"discovered '{discovered[mod]}', resolved '{res_real}'.",
                file=sys.stderr,
            )
            sys.exit(1)
        actual_sha = sha256_file(res_real)
        if actual_sha != exp_sha:
            print(
                f"❌ FAIL: Artifact SHA-256 mismatch for '{mod}' ({res_real}): "
                f"expected {exp_sha}, got {actual_sha}.",
                file=sys.stderr,
            )
            sys.exit(1)
        verified[mod] = (res_real, actual_sha)
    return verified


def run_source_frontend_audit(
    mod: str,
    src_path: str,
    expected_src_sha: str,
    discovered_oleans: dict[str, str],
    expected_oleans: dict[str, tuple[str, str]],
) -> tuple[int, int]:
    """Elaborate `src_path` through Lean's Frontend with `infoState.enabled := true` and audit
    100% of persistent AND transient (`example` / `withoutModifyingEnv`) kernel declarations
    via `(env.setExporting false).checked.get.constants.foldStage2` and `Lean.collectAxioms`.
    Returns (audited_decl_snapshots, audited_example_count).
    """
    if not os.path.isfile(src_path):
        print(f"❌ FAIL: Missing source file '{src_path}' for module '{mod}'.", file=sys.stderr)
        sys.exit(1)
    actual_before = sha256_file(src_path)
    if actual_before != expected_src_sha:
        print(
            f"❌ FAIL: Source SHA-256 mismatch before frontend audit of '{mod}' ({src_path}): "
            f"expected {expected_src_sha}, got {actual_before}.",
            file=sys.stderr,
        )
        sys.exit(1)

    with tempfile.TemporaryDirectory(prefix="catsem_src_audit_") as tmpdir:
        driver_path = os.path.join(tmpdir, "FrontendAudit.lean")
        report_path = os.path.join(tmpdir, "src_report.tsv")
        src_lit = json.dumps(os.path.realpath(src_path))
        report_lit = json.dumps(report_path)

        lean_src = f"""import Lean

def collectAxiomsInEnv (env : Lean.Environment) (cName : Lean.Name) : IO (Array Lean.Name) := do
  let ctx : Lean.Core.Context := {{ fileName := {src_lit}, fileMap := default }}
  let st : Lean.Core.State := {{ env := env }}
  let (axs, _) ← Lean.Core.CoreM.toIO (Lean.collectAxioms cName) ctx st
  return axs

partial def countExamples (stx : Lean.Syntax) : Nat := Id.run do
  let k := stx.getKind
  if k == ``Lean.Parser.Term.quot then
    return 0
  let mut n := if k == ``Lean.Parser.Command.example then 1 else 0
  for arg in stx.getArgs do
    n := n + countExamples arg
  return n

def isExampleDeclName (n : Lean.Name) : Bool :=
  match n.eraseMacroScopes with
  | .str _ "_example" => true
  | _ => false

def isBenignMathlibModuleWarn (txt : String) : Bool :=
  (txt.splitOn "imports `Mathlib.").length > 1 &&
    (txt.splitOn "which is designed for use with the module system").length > 1

unsafe def main : IO UInt32 := do
  let srcPath : System.FilePath := System.FilePath.mk {src_lit}
  let reportPath : System.FilePath := System.FilePath.mk {report_lit}
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let src ← IO.FS.readFile srcPath
  let inputCtx := Lean.Parser.mkInputContext src srcPath.toString
  let (header, parserState, messages) ← Lean.Parser.parseHeader inputCtx
  let mut outLines : Array String := #[]
  for imp in Lean.Elab.headerToImports header do
    let p ← Lean.findOLean imp.module
    let rp ← IO.FS.realPath p
    outLines := outLines.push s!"IMP_OLEAN\\t{{imp.module}}\\t{{rp}}"
  let (headerEnv, messages) ← Lean.Elab.processHeader header {{}} messages inputCtx (mainModule := `_CatSemSrcAudit.{mod})
  let cmdState := {{ Lean.Elab.Command.mkState headerEnv messages {{}} with infoState.enabled := true }}
  let s ← Lean.Elab.IO.processCommands inputCtx parserState cmdState
  for m in s.commandState.messages.toList do
    let txt ← m.toString
    match m.severity with
    | .error =>
      IO.eprintln s!"FRONTEND ERROR in {{srcPath}}: {{txt}}"
      return 1
    | .warning =>
      if !isBenignMathlibModuleWarn txt then
        IO.eprintln s!"FORBIDDEN COMPILER WARNING in {{srcPath}}: {{txt}}"
        return 1
    | .information => pure ()
  if !s.commandState.infoState.enabled then
    IO.eprintln s!"FORBIDDEN: infoState.enabled was disabled during elaboration of {{srcPath}}"
    return 1
  let mut expectedExamples : Nat := 0
  for cmd in s.commands do
    expectedExamples := expectedExamples + countExamples cmd
  let seenEnvPtrs ← IO.mkRef ({{}} : Std.HashSet USize)
  let auditedExamples ← IO.mkRef (0 : Nat)
  let auditedDecls ← IO.mkRef (0 : Nat)
  let auditError ← IO.mkRef (none : Option String)
  let auditEnv (e : Lean.Environment) : IO Unit := do
    if (← auditError.get).isSome then
      return
    let privKEnv := (e.setExporting false).checked.get
    let addr := ptrAddrUnsafe privKEnv
    let seen ← seenEnvPtrs.get
    if !seen.contains addr then
      seenEnvPtrs.set (seen.insert addr)
      let localDecls := privKEnv.constants.foldStage2 (fun acc n ci => acc.push (n, ci)) #[]
      for (cName, cInfo) in localDecls do
        if (← auditError.get).isNone then
          let isEx := isExampleDeclName cName
          if isEx then
            auditedExamples.modify (· + 1)
          let isAx := match cInfo with | .axiomInfo _ => true | _ => false
          if isEx && cInfo.isUnsafe then
            auditError.set (some s!"FORBIDDEN UNSAFE EXAMPLE '{{cName}}' in '{{srcPath}}'")
          else if isAx then
            auditError.set (some s!"FORBIDDEN LOCAL AXIOM '{{cName}}' in '{{srcPath}}'")
          else if !cInfo.isUnsafe then
            auditedDecls.modify (· + 1)
            let axs ← collectAxiomsInEnv e cName
            for ax in axs do
              if ax != ``propext && ax != ``Quot.sound then
                if (← auditError.get).isNone then
                  auditError.set (some s!"FORBIDDEN AXIOM '{{ax}}' transitively used by '{{cName}}' in '{{srcPath}}'")
  auditEnv s.commandState.env
  for tree in s.commandState.infoState.trees do
    let _ ← tree.visitM (m := IO) (postNode := fun ci _ _ _ => do
      auditEnv ci.env
      pure ())
    pure ()
  if let some errMsg ← auditError.get then
    IO.eprintln errMsg
    return 1
  let actualEx ← auditedExamples.get
  if actualEx != expectedExamples then
    IO.eprintln s!"FATAL: Example audit count mismatch in '{{srcPath}}': parsed={{expectedExamples}}, audited={{actualEx}}"
    return 1
  let totalDecls ← auditedDecls.get
  outLines := outLines.push s!"SRC_OK\\t{mod}\\t{{totalDecls}}\\t{{actualEx}}"
  IO.FS.writeFile reportPath (String.intercalate "\\n" outLines.toList ++ "\\n")
  return 0
"""
        with open(driver_path, "w", encoding="utf-8") as f:
            f.write(lean_src)

        proc = subprocess.run(
            ["lake", "env", "lean", "--run", driver_path],
            capture_output=True,
            text=True,
        )
        if proc.returncode != 0 or not os.path.exists(report_path):
            sys.stdout.write(proc.stdout)
            sys.stderr.write(proc.stderr)
            print(f"❌ FAIL: Frontend source/example audit failed for '{mod}' ({src_path})!", file=sys.stderr)
            sys.exit(1)

        src_ok_seen = False
        decl_cnt = 0
        ex_cnt = 0
        with open(report_path, "r", encoding="utf-8") as rf:
            for raw_line in rf:
                line = raw_line.rstrip("\r\n")
                if not line:
                    continue
                parts = line.split("\t")
                if parts[0] == "IMP_OLEAN" and len(parts) == 3:
                    imp_mod, imp_path = parts[1], os.path.realpath(parts[2])
                    if imp_mod.startswith(PROJECT_MOD_PREFIXES):
                        if imp_mod in discovered_oleans and discovered_oleans[imp_mod] != imp_path:
                            print(
                                f"❌ FAIL: Frontend import '{imp_mod}' resolved to '{imp_path}', "
                                f"expected '{discovered_oleans[imp_mod]}'.",
                                file=sys.stderr,
                            )
                            sys.exit(1)
                        if imp_mod in expected_oleans and expected_oleans[imp_mod][0] != imp_path:
                            print(
                                f"❌ FAIL: Frontend import '{imp_mod}' resolved to '{imp_path}', "
                                f"expected bound path '{expected_oleans[imp_mod][0]}'.",
                                file=sys.stderr,
                            )
                            sys.exit(1)
                elif parts[0] == "SRC_OK" and len(parts) == 4 and parts[1] == mod:
                    src_ok_seen = True
                    decl_cnt = int(parts[2])
                    ex_cnt = int(parts[3])
                else:
                    print(f"❌ FAIL: Unexpected frontend audit report line: {line}", file=sys.stderr)
                    sys.exit(1)

        if not src_ok_seen:
            print(f"❌ FAIL: Missing SRC_OK confirmation for '{mod}'.", file=sys.stderr)
            sys.exit(1)

    actual_after = sha256_file(src_path)
    if actual_after != expected_src_sha:
        print(
            f"❌ FAIL: Source file '{src_path}' changed during audit "
            f"({expected_src_sha} -> {actual_after}).",
            file=sys.stderr,
        )
        sys.exit(1)

    return decl_cnt, ex_cnt


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Fail-closed Lean .olean + Frontend example/transient-declaration kernel auditor."
    )
    parser.add_argument(
        "--resolve-olean",
        type=str,
        default=None,
        help="Check for ambiguous .oleans and print canonical Lean.findOLean path for MODULE.",
    )
    parser.add_argument(
        "--verify-olean",
        action="append",
        default=[],
        help="Verify MOD=PATH:SHA256 matches Lean.findOLean and has zero ambiguous shadows.",
    )
    parser.add_argument(
        "--expect-olean",
        action="append",
        default=[],
        help="Bind audited module MOD=PATH:SHA256 before and after auditing.",
    )
    parser.add_argument(
        "--expect-source",
        action="append",
        default=[],
        help="Bind audited module source MOD=SRC_PATH:SHA256 before and after frontend elaboration.",
    )
    parser.add_argument("mods", nargs="*", help="Module names to audit (e.g. Specs.Defs Specs.RedTeam).")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    discovered = check_no_ambiguous_project_oleans()

    if args.resolve_olean is not None:
        mod = args.resolve_olean.strip()
        resolved = resolve_oleans_via_lean([mod])[mod]
        if mod in discovered and discovered[mod] != resolved:
            print(
                f"❌ FAIL: Ambiguous resolution for '{mod}': discovered '{discovered[mod]}' vs Lean.findOLean '{resolved}'.",
                file=sys.stderr,
            )
            return 1
        print(resolved)
        return 0

    verify_map: dict[str, tuple[str, str]] = {}
    for spec in args.verify_olean:
        mod, path_part, sha_part = parse_binding_spec(spec, "--verify-olean")
        verify_map[mod] = (path_part, sha_part)

    if verify_map:
        verify_olean_bindings(verify_map, discovered)
        if not args.mods:
            return 0

    mods = [m.strip() for m in args.mods if m.strip()]
    if not mods:
        print("❌ FAIL: audit_modules.py requires at least one module name.", file=sys.stderr)
        return 1

    for m in mods:
        if not is_valid_mod_name(m):
            print(f"❌ FAIL: Invalid module identifier '{m}'.", file=sys.stderr)
            return 1

    expect_olean_map: dict[str, tuple[str, str]] = dict(verify_map)
    for spec in args.expect_olean:
        mod, path_part, sha_part = parse_binding_spec(spec, "--expect-olean")
        expect_olean_map[mod] = (path_part, sha_part)

    # Resolve all target modules via Lean.findOLean and pin pre-audit SHA-256 even if --expect-olean omitted
    resolved_targets = resolve_oleans_via_lean(mods)
    for m in mods:
        res_path = resolved_targets[m]
        if m in discovered and discovered[m] != res_path:
            print(
                f"❌ FAIL: Search-path mismatch for '{m}': discovered '{discovered[m]}' vs Lean.findOLean '{res_path}'.",
                file=sys.stderr,
            )
            return 1
        cur_sha = sha256_file(res_path)
        if m in expect_olean_map:
            exp_real = os.path.realpath(expect_olean_map[m][0])
            exp_sha = expect_olean_map[m][1]
            if res_path != exp_real or cur_sha != exp_sha:
                print(
                    f"❌ FAIL: Pre-audit .olean binding mismatch for '{m}': "
                    f"expected {exp_real}:{exp_sha}, got {res_path}:{cur_sha}.",
                    file=sys.stderr,
                )
                return 1
        else:
            expect_olean_map[m] = (res_path, cur_sha)

    expect_src_map: dict[str, tuple[str, str]] = {}
    for spec in args.expect_source:
        mod, path_part, sha_part = parse_binding_spec(spec, "--expect-source")
        expect_src_map[mod] = (path_part, sha_part)

    for m in mods:
        default_src = m.replace(".", "/") + ".lean"
        if m in expect_src_map:
            src_p, src_sha = expect_src_map[m]
            if not os.path.isfile(src_p):
                print(f"❌ FAIL: Expected source file '{src_p}' for '{m}' does not exist.", file=sys.stderr)
                return 1
            if sha256_file(src_p) != src_sha:
                print(f"❌ FAIL: Pre-audit source SHA-256 mismatch for '{m}' ({src_p}).", file=sys.stderr)
                return 1
        else:
            if not os.path.isfile(default_src):
                print(f"❌ FAIL: Missing source file '{default_src}' for audited module '{m}'.", file=sys.stderr)
                return 1
            expect_src_map[m] = (default_src, sha256_file(default_src))

    imports_src = "\n".join(f"import {m}" for m in mods)
    target_array = ", ".join(f"`{m}" for m in mods)

    with tempfile.TemporaryDirectory(prefix="catsem_mod_audit_") as tmpdir:
        report_path = os.path.join(tmpdir, "report.tsv")
        report_path_lit = json.dumps(report_path)
        driver_path = os.path.join(tmpdir, "AuditDriver.lean")

        lean_src = f"""import Lean
{imports_src}

open Lean Elab Command in
#eval show CommandElabM Unit from do
  if (← searchPathRef.get).isEmpty then
    Lean.initSearchPath (← Lean.findSysroot)
  let env ← getEnv
  let targetMods : Array Name := #[{target_array}]
  let allowedAxioms : Array Name := #[`propext, `Quot.sound]
  let reportPath : System.FilePath := System.FilePath.mk {report_path_lit}
  let mut lines : Array String := #[]
  for m in targetMods do
    if !(env.header.moduleNames.contains m) then
      throwError s!"FATAL: Module '{{m}}' missing from imported environment"
    let oleanPath ← liftM (Lean.findOLean m >>= IO.FS.realPath : IO System.FilePath)
    lines := lines.push s!"OLEAN\\t{{m}}\\t{{oleanPath}}"
  let mut idx : Nat := 0
  for modName in env.header.moduleNames do
    if targetMods.contains modName then
      match env.header.moduleData[idx]? with
      | none => throwError s!"FATAL: Missing moduleData for '{{modName}}'"
      | some modData =>
        let mut cnt : Nat := 0
        for cinfo in modData.constants do
          let declName := cinfo.name
          let isAx := match cinfo with | .axiomInfo _ => true | _ => false
          if !(cinfo.isUnsafe && !isAx) then
            if isAx then
              throwError s!"FORBIDDEN LOCAL AXIOM '{{declName}}' declared in '{{modName}}'"
            let axs ← Lean.collectAxioms declName
            for ax in axs do
              if !(allowedAxioms.contains ax) then
                throwError s!"FORBIDDEN AXIOM '{{ax}}' transitively used by '{{declName}}' in '{{modName}}'"
            let axStr := String.intercalate "," (axs.toList.map toString)
            lines := lines.push s!"DECL\\t{{modName}}\\t{{declName}}\\t{{axStr}}"
            cnt := cnt + 1
        if cnt == 0 then
          throwError s!"FATAL: Module '{{modName}}' contributed 0 audited declarations"
        lines := lines.push s!"MOD\\t{{modName}}\\t{{cnt}}"
    idx := idx + 1
  liftM (IO.FS.writeFile reportPath (String.intercalate "\\n" lines.toList ++ "\\n") : IO Unit)
"""
        with open(driver_path, "w", encoding="utf-8") as f:
            f.write(lean_src)

        proc = subprocess.run(
            ["lake", "env", "lean", driver_path],
            capture_output=True,
            text=True,
        )
        if proc.returncode != 0:
            sys.stdout.write(proc.stdout)
            sys.stderr.write(proc.stderr)
            print("❌ FAIL: Kernel module-enumeration audit failed in Lean!", file=sys.stderr)
            return 1

        if not os.path.exists(report_path):
            print("❌ FAIL: Audit report file was not created!", file=sys.stderr)
            return 1

        seen_decls: dict[str, set[str]] = {m: set() for m in mods}
        mod_expected: dict[str, int] = {}
        driver_oleans: dict[str, str] = {}

        with open(report_path, "r", encoding="utf-8") as rf:
            for raw_line in rf:
                line = raw_line.rstrip("\r\n")
                if not line:
                    continue
                parts = line.split("\t")
                if parts[0] == "OLEAN" and len(parts) == 3:
                    _, mod_name, olean_p = parts
                    driver_oleans[mod_name] = os.path.realpath(olean_p)
                elif parts[0] == "DECL" and len(parts) == 4:
                    _, mod_name, decl_name, ax_csv = parts
                    if mod_name not in seen_decls:
                        print(f"❌ FAIL: Unexpected module '{mod_name}' in report.", file=sys.stderr)
                        return 1
                    if decl_name in seen_decls[mod_name]:
                        print(f"❌ FAIL: Duplicate declaration '{decl_name}' in '{mod_name}'.", file=sys.stderr)
                        return 1
                    axs = [a for a in ax_csv.split(",") if a]
                    bad = [a for a in axs if a not in ALLOWED]
                    if bad:
                        print(f"❌ FAIL: '{decl_name}' ({mod_name}) uses forbidden axiom(s): {bad}", file=sys.stderr)
                        return 1
                    seen_decls[mod_name].add(decl_name)
                elif parts[0] == "MOD" and len(parts) == 3:
                    _, mod_name, cnt_str = parts
                    mod_expected[mod_name] = int(cnt_str)
                else:
                    print(f"❌ FAIL: Malformed audit report line: {line}", file=sys.stderr)
                    return 1

        for m in mods:
            exp_real, exp_sha = expect_olean_map[m]
            if driver_oleans.get(m) != exp_real:
                print(
                    f"❌ FAIL: AuditDriver imported '{driver_oleans.get(m)}' for '{m}', expected '{exp_real}'.",
                    file=sys.stderr,
                )
                return 1
            if sha256_file(exp_real) != exp_sha:
                print(f"❌ FAIL: .olean SHA-256 changed during module audit for '{m}'.", file=sys.stderr)
                return 1

        summary_parts = []
        total = 0
        for m in mods:
            actual = len(seen_decls[m])
            expected = mod_expected.get(m, -1)
            if actual <= 0 or actual != expected:
                print(f"❌ FAIL: Coverage mismatch for {m}: actual={actual}, expected={expected}", file=sys.stderr)
                return 1
            summary_parts.append(f"{m}={actual}")
            total += actual

    # Run Frontend source + transient/anonymous `example` kernel audit on every audited module
    src_summaries = []
    for m in mods:
        src_p, src_sha = expect_src_map[m]
        decl_snapshots, ex_cnt = run_source_frontend_audit(
            m, src_p, src_sha, discovered, expect_olean_map
        )
        src_summaries.append(f"{m}[examples={ex_cnt}]")

    # Final post-audit verification of all bound .oleans and ambiguity check
    discovered_after = check_no_ambiguous_project_oleans()
    verify_olean_bindings(expect_olean_map, discovered_after)

    print(
        f"✅ Complete module & frontend-example axiom audit passed across {total} kernel declarations "
        f"({', '.join(summary_parts)}; {', '.join(src_summaries)}; allowed={sorted(ALLOWED)})."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
