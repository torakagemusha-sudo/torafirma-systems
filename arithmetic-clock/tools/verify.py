"""Fail-closed verifier for a relocatable arithmetic-clock Lean package."""
from __future__ import annotations

import argparse
import errno
import hashlib
import json
import math
import os
import re
import shutil
import subprocess
import sys
import tempfile
import stat
import threading
from dataclasses import dataclass
from pathlib import Path
from typing import Any

# Direct CLI execution must preserve the exact public input tree.
sys.dont_write_bytecode = True

try:
    from .pack_common import (ALLOWED_AXIOMS, LEAN_COMMIT, LEAN_VERSION, MATHLIB_REVISION,
        BUILD_ORDER, MODULES, ROOT_NAMESPACE, is_external, local_source_path, parse_imports, safe_relative,
        scan_lean, sha256_file, topo_sort, has_absolute_host_path, has_compiled_host_path, add_exception_note)
except ImportError:  # Direct CLI execution has no package parent.
    from pack_common import (ALLOWED_AXIOMS, LEAN_COMMIT, LEAN_VERSION, MATHLIB_REVISION,
        BUILD_ORDER, MODULES, ROOT_NAMESPACE, is_external, local_source_path, parse_imports, safe_relative,
        scan_lean, sha256_file, topo_sort, has_absolute_host_path, has_compiled_host_path, add_exception_note)


CERTIFICATES = ("SOURCE_CERTIFICATE.json", "BUILD_CERTIFICATE.json",
    "DECLARATION_CERTIFICATE.json", "AXIOM_CERTIFICATE.json", "CONTROL_CERTIFICATE.json",
    "PRIVACY_CERTIFICATE.json", "REPRODUCIBILITY_CERTIFICATE.json")
OBJECT_SUFFIXES = frozenset((".olean", ".ilean", ".trace", ".log"))
ENTRIES = ("ArithmeticClock.DivisorGram60", "ArithmeticClock.ContinuousReturn60", "ArithmeticClock.IntegerClock60")
ROOT_KEYS = frozenset(("schema_version", "project", "toolchain", "modules", "entries", "declarations",
    "allowed_axioms", "negative_controls", "facade", "kind_totals", "public_files"))
CONTROL_SHA256 = "fad53d5c2641f778c598a9acb80667ed964e576a6ea78d4b071f522c6c44535b"
POLICY_CONTRACT = frozenset(((8, "a441d15d9ddb3eb27eb32589872fe1f057188adb360656e6b809a1aa83bb7bf9"),
    (8, "3922a0cad9b4327aae24e9be6708eddb42fe0e6f29d53460bae7a9a1a19fa3d0"),
    (7, "641ba11fd30ddff45a0b2f0255ee0e96e0e58d133b7f6b14afbd306a6f784d02"),
    (7, "804009875b8f147428508e89ac1fbcda6d9be01b56a5818e31b288b77706e61a"),
    (10, "89e1de7cdfeddd4d55f3c330e576b517fe36878b35fe1ff9ba0ba9a5c6457ece"),
    (14, "b9e2a4bcd957695b6bdf80538330c1b46bc1f2b47930a93209a356935aa6cdd7")))
DEPENDENCY_PINS = {
    "plausible": "77e08eddc486491d7b9e470926b3dbe50319451a", "LeanSearchClient": "25078369972d295301f5a1e53c3e5850cf6d9d4c",
    "importGraph": "e6a9f0f5ee3ccf7443a0070f92b62f8db12ae82b", "proofwidgets": "c4919189477c3221e6a204008998b0d724f49904",
    "aesop": "5d50b08dedd7d69b3d9b3176e0d58a23af228884", "Qq": "fa4f7f15d97591a9cf3aa7724ba371c7fc6dda02",
    "batteries": "f5d04a9c4973d401c8c92500711518f7c656f034", "Cli": "02dbd02bc00ec4916e99b04b2245b30200e200d0"}
DEPENDENCY_ORDER = tuple(DEPENDENCY_PINS)
DEPENDENCY_ROWS = {
    "plausible": ("https://github.com/leanprover-community/plausible", "leanprover-community", "main", False, "lakefile.toml"),
    "LeanSearchClient": ("https://github.com/leanprover-community/LeanSearchClient", "leanprover-community", "main", False, "lakefile.toml"),
    "importGraph": ("https://github.com/leanprover-community/import-graph", "leanprover-community", "main", False, "lakefile.toml"),
    "proofwidgets": ("https://github.com/leanprover-community/ProofWidgets4", "leanprover-community", "v0.0.57", False, "lakefile.lean"),
    "aesop": ("https://github.com/leanprover-community/aesop", "leanprover-community", "master", False, "lakefile.toml"),
    "Qq": ("https://github.com/leanprover-community/quote4", "leanprover-community", "master", False, "lakefile.toml"),
    "batteries": ("https://github.com/leanprover-community/batteries", "leanprover-community", "main", False, "lakefile.toml"),
    "Cli": ("https://github.com/leanprover/lean4-cli", "leanprover", "main", True, "lakefile.toml"),
}
MATHLIB_MANIFEST_SHA256 = "5c6421b650bc87a2427a892a39e5522dc44543ca4ac1bd6e9f08d536c044a752"
CLAIM_ENDPOINT_SET_SHA256 = "94f07478d426194dc4e28e7b1191fdf69eb490d34b8acaa5cb0ce6d085c3ad86"
CLAIM_ROWS_SHA256 = "ebc9ab9f72413eb94a317af7f0bbfb1d717a1fa3f8ef4ae1908b5290e4e11d7c"
CONTROL_DIGESTS = {"invalid_false": "e6c1083c2f2bedba0ec47f8076f79c5a88585f2929c94090b4514e0a4cf65308",
    "wrong_period": "4ecf3f87b6d284288d952c5d14178910b2ae475684f6c8c51496c356ea00f2c9"}
DECLARATION_CONTRACT_SHA256 = "e1f0011a859822ad9f1170588329e6d3e681e2d23c2e1c93138edcd4ef4c8975"
KIND_TOTALS = {"theorem": 161, "def": 41, "abbrev": 1}
PUBLIC_STATIC_PATHS = frozenset(("ArithmeticClock.lean", "controls/WrongPeriod.lean", "README.md", "LICENSE",
    "__init__.py", "tools/__init__.py", "tools/pack_common.py", "tools/verify.py", "tools/package_release.py", "tests/test_verify.py",
    "lean-toolchain", "lakefile.toml", "DEPENDENCIES.json", "CLAIM_MAP.json"))
OWNER_BY_MODULE = {**{module: module for module in MODULES[:7]},
    "ArithmeticClock.ContinuousReturn60": "ArithmeticClock.RealClock60",
    "ArithmeticClock.IntegerClock60": "ArithmeticClock.RealClock60"}
REGEX_WORD_BOUNDARY = chr(92) + "b"


class VerificationError(RuntimeError):
    pass


@dataclass(frozen=True)
class Module:
    name: str
    source: str
    sha256: str
    bytes: int
    imports: tuple[str, ...]


@dataclass(frozen=True)
class Declaration:
    name: str
    module: str
    kind: str


@dataclass(frozen=True)
class Control:
    name: str
    source: str
    sha256: str


@dataclass(frozen=True)
class Config:
    package: Path
    root: Path
    policy: Path
    policy_sha256: str
    policy_tokens: tuple[str, ...]
    package_sha256: str
    modules: tuple[Module, ...]
    entries: tuple[str, ...]
    declarations: tuple[Declaration, ...]
    controls: tuple[Control, ...]
    facade: str
    facade_sha256: str
    facade_bytes: int
    kind_totals: dict[str, int] | None
    public_files: tuple[tuple[str, str, int], ...]


@dataclass
class VerificationResult:
    config: Config
    module_order: list[str]
    audit: dict[str, tuple[str, list[str]]]
    controls: dict[str, Any]
    build: dict[str, Any]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


def _read_regular_bytes(path: Path, message: str) -> bytes:
    try:
        mode = path.lstat().st_mode
    except OSError as exc:
        raise VerificationError(message) from exc
    require(not path.is_symlink() and stat.S_ISREG(mode), message)
    try:
        return path.read_bytes()
    except OSError as exc:
        raise VerificationError(message) from exc


def _json(path: Path) -> dict[str, Any]:
    try:
        def no_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
            value: dict[str, Any] = {}
            for key, item in pairs:
                if key in value:
                    raise VerificationError("duplicate JSON key")
                value[key] = item
            return value
        value = json.loads(_read_regular_bytes(path, "invalid JSON configuration").decode("utf-8"), object_pairs_hook=no_duplicates,
            parse_constant=lambda _: (_ for _ in ()).throw(VerificationError("nonfinite JSON number")))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise VerificationError("invalid JSON configuration") from exc
    require(isinstance(value, dict), "configuration must be an object")
    return value


def _sha(value: Any) -> bool:
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None


def _contract_bytes(value: Any) -> bytes:
    """Encode a reviewed digest contract without certificate newline framing."""
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def _validate_claim_map(root: Path, declarations: tuple[Declaration, ...]) -> None:
    path = root / "CLAIM_MAP.json"
    require(path.is_file() and not path.is_symlink(), "claim map is missing")
    raw = _json(path)
    require(set(raw) == {"schema_version", "claims"} and type(raw.get("schema_version")) is int and
            raw.get("schema_version") == 1 and
            isinstance(raw.get("claims"), list) and len(raw["claims"]) == 12, "claim map schema differs")
    endpoints: list[str] = []
    identifiers: set[str] = set()
    rows: list[tuple[str, str, tuple[str, ...]]] = []
    for row in raw["claims"]:
        require(isinstance(row, dict) and set(row) == {"id", "kind", "endpoints"} and isinstance(row.get("id"), str) and
                row["id"] and isinstance(row.get("kind"), str) and row["kind"] and isinstance(row.get("endpoints"), list) and row["endpoints"],
                "claim map row differs")
        require(row["id"] not in identifiers, "duplicate claim map row")
        identifiers.add(row["id"])
        require(all(isinstance(endpoint, str) for endpoint in row["endpoints"]), "claim endpoint differs")
        endpoints.extend(row["endpoints"])
        rows.append((row["id"], row["kind"], tuple(row["endpoints"])))
    require(len(endpoints) == 76 and len(set(endpoints)) == 73 and set(endpoints) <= {item.name for item in declarations},
            "claim map endpoint count differs")
    endpoint_digest = hashlib.sha256(_contract_bytes(sorted(set(endpoints)))).hexdigest()
    rows_digest = hashlib.sha256(_contract_bytes(rows)).hexdigest()
    require(endpoint_digest == CLAIM_ENDPOINT_SET_SHA256 and rows_digest == CLAIM_ROWS_SHA256,
            "claim map endpoint contract differs")


def _validate_public_pins(root: Path) -> None:
    try:
        require(_read_regular_bytes(root / "lean-toolchain", "lean toolchain pin differs") ==
                b"leanprover/lean4:v4.19.0\n", "lean toolchain pin differs")
        lake = _read_regular_bytes(root / "lakefile.toml", "lake configuration differs")
        newline = bytes((10,))
        expected_lake = newline.join((b'name = "arithmetic-clock"', b'', b'[[lean_lib]]',
            b'name = "ArithmeticClock"', b'', b'[[require]]', b'name = "mathlib"',
            b'git = "https://github.com/leanprover-community/mathlib4.git"',
            b'rev = "' + MATHLIB_REVISION.encode("ascii") + b'"', b''))
        require(lake == expected_lake, "lakefile pin differs")
        dependencies_path = root / "DEPENDENCIES.json"
        _read_regular_bytes(dependencies_path, "dependency pins differ")
        dependencies = _json(dependencies_path)
    except (OSError, UnicodeDecodeError) as exc:
        raise VerificationError("public pin file is unreadable") from exc
    require(type(dependencies.get("schema_version")) is int and
            dependencies == {"schema_version": 1, "dependencies": DEPENDENCY_PINS}, "dependency pins differ")


def load_config(package: Path, privacy_policy: Path) -> Config:
    package_input, policy_input = Path(package), Path(privacy_policy)
    require(package_input.is_file() and not package_input.is_symlink(), "missing package configuration")
    require(policy_input.is_file() and not policy_input.is_symlink(), "missing external privacy policy")
    package, privacy_policy = package_input.resolve(), policy_input.resolve()
    require(not privacy_policy.is_relative_to(package.parent), "privacy policy must be external")
    raw = _json(package)
    require(set(raw) <= ROOT_KEYS and set(raw) >= ROOT_KEYS - {"kind_totals"}, "unknown or missing configuration key")
    require(type(raw.get("schema_version")) is int and raw.get("schema_version") == 1 and raw.get("project") == "arithmetic-clock", "unsupported schema")
    require(raw.get("toolchain") == {"lean_version": LEAN_VERSION, "lean_commit": LEAN_COMMIT,
        "mathlib_revision": MATHLIB_REVISION}, "unexpected toolchain pins")
    policy_hash = sha256_file(privacy_policy)
    policy = _json(privacy_policy)
    require(set(policy) == {"schema_version", "blocked"} and type(policy.get("schema_version")) is int and policy["schema_version"] == 1 and
            isinstance(policy.get("blocked"), list) and all(isinstance(x, str) and x for x in policy["blocked"]),
            "external privacy policy is malformed")
    require(len(set(policy["blocked"])) == len(policy["blocked"]), "external privacy policy duplicates a token")
    require(frozenset((len(item), hashlib.sha256(item.encode("utf-8")).hexdigest()) for item in policy["blocked"]) == POLICY_CONTRACT,
            "external privacy policy contract differs")
    rows = raw.get("modules")
    require(isinstance(rows, list) and len(rows) == len(MODULES), "exact module allowlist required")
    modules: list[Module] = []
    for row in rows:
        require(isinstance(row, dict) and set(row) == {"module", "source", "sha256", "bytes", "imports"}, "invalid module row")
        name, source, digest, size, imports = (row.get("module"), row.get("source"), row.get("sha256"),
            row.get("bytes"), row.get("imports"))
        require(isinstance(name, str) and name in MODULES and source == local_source_path(name), "invalid module source")
        require(_sha(digest) and type(size) is int and size >= 0 and isinstance(imports, list), "invalid module binding")
        require(all(isinstance(x, str) for x in imports), "invalid module imports")
        modules.append(Module(name, source, digest, size, tuple(imports)))
    require(tuple(item.name for item in modules) == MODULES, "module order or allowlist differs")
    entries = raw.get("entries")
    require(entries == list(ENTRIES), "exact entry modules required")
    declared = raw.get("declarations")
    require(isinstance(declared, list) and len(declared) == 203, "exactly 203 declarations required")
    declarations: list[Declaration] = []
    for row in declared:
        require(isinstance(row, dict) and set(row) == {"name", "module", "kind"}, "invalid declaration row")
        name, module, kind = row.get("name"), row.get("module"), row.get("kind")
        require(isinstance(name, str) and name.startswith(ROOT_NAMESPACE + ".") and module in MODULES and
                kind in ("theorem", "def", "abbrev"), "invalid declaration selection")
        declarations.append(Declaration(name, module, kind))
    require(len({item.name for item in declarations}) == 203, "duplicate declaration selection")
    require(sum(item.module == MODULES[0] for item in declarations) == 6 and
            sum(item.module != MODULES[0] for item in declarations) == 197, "invalid declaration module totals")
    kind_totals = raw.get("kind_totals")
    require(kind_totals == KIND_TOTALS, "declaration kind totals differ")
    contract_rows = sorted((item.module, item.name, item.kind) for item in declarations)
    require(hashlib.sha256(json.dumps(contract_rows, separators=(",", ":"), ensure_ascii=True).encode("ascii")).hexdigest() ==
            DECLARATION_CONTRACT_SHA256, "declaration contract differs")
    require(raw.get("allowed_axioms") == sorted(ALLOWED_AXIOMS), "allowed axiom set differs")
    controls_raw = raw.get("negative_controls")
    require(isinstance(controls_raw, list) and len(controls_raw) == 1, "exact negative controls required")
    controls: list[Control] = []
    for row in controls_raw:
        require(isinstance(row, dict) and set(row) == {"name", "source", "sha256"}, "invalid control row")
        name, source, digest = row.get("name"), row.get("source"), row.get("sha256")
        require(isinstance(name, str) and re.fullmatch(r"[a-z][a-z_0-9]*", name) and isinstance(source, str) and _sha(digest),
                "invalid control binding")
        controls.append(Control(name, source, digest))
    require({item.name for item in controls} >= {"wrong_period"}, "wrong-period control required")
    require(controls[0].source == "controls/WrongPeriod.lean" and controls[0].sha256 == CONTROL_SHA256,
            "wrong-period control binding differs")
    facade_row = raw.get("facade")
    require(isinstance(facade_row, dict) and set(facade_row) == {"source", "sha256", "bytes", "imports"} and
            facade_row.get("source") == "ArithmeticClock.lean" and _sha(facade_row.get("sha256")) and
            type(facade_row.get("bytes")) is int and facade_row["bytes"] >= 0 and facade_row.get("imports") == list(ENTRIES),
            "facade binding differs")
    facade = facade_row["source"]
    public_rows = raw.get("public_files")
    require(isinstance(public_rows, list), "public input table is required")
    public_files: list[tuple[str, str, int]] = []
    for row in public_rows:
        require(isinstance(row, dict) and set(row) == {"path", "sha256", "bytes"} and isinstance(row["path"], str) and
                _sha(row["sha256"]) and type(row["bytes"]) is int and row["bytes"] >= 0, "invalid public input row")
        safe_relative(row["path"])
        public_files.append((row["path"], row["sha256"], row["bytes"]))
    expected_paths = {item.source for item in modules} | {facade} | {item.source for item in controls}
    table_paths = {path for path, _, _ in public_files}
    require(table_paths == expected_paths | PUBLIC_STATIC_PATHS and len(table_paths) == len(public_files),
            "public input table differs")
    _validate_claim_map(package.parent, tuple(declarations))
    _validate_public_pins(package.parent)
    return Config(package, package.parent, privacy_policy, policy_hash, tuple(policy["blocked"]), sha256_file(package), tuple(modules), tuple(entries),
                  tuple(declarations), tuple(controls), facade, facade_row["sha256"], facade_row["bytes"], kind_totals, tuple(public_files))


def _package_file(config: Config, relative: str) -> Path:
    try:
        safe_relative(relative)
    except ValueError as exc:
        raise VerificationError("invalid package path") from exc
    path = config.root / relative
    require(path.is_file(), "missing package file: " + relative)
    require(not path.is_symlink() and path.resolve().is_relative_to(config.root.resolve()), "symlinked package file")
    return path


def _policy_tokens(config: Config) -> tuple[str, ...]:
    return config.policy_tokens


def _inspectable_json(text: str) -> Any:
    def no_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        value: dict[str, Any] = {}
        for key, item in pairs:
            require(key not in value, "duplicate JSON key in inspectable file")
            value[key] = item
        return value

    def finite_float(value: str) -> float:
        parsed = float(value)
        require(math.isfinite(parsed), "nonfinite JSON number in inspectable file")
        return parsed

    try:
        return json.loads(text, object_pairs_hook=no_duplicates,
                          parse_float=finite_float,
                          parse_constant=lambda _: (_ for _ in ()).throw(
                              VerificationError("nonfinite JSON number in inspectable file")))
    except json.JSONDecodeError as exc:
        raise VerificationError("invalid JSON inspectable file") from exc


def _json_strings(value: Any) -> list[str]:
    if isinstance(value, str):
        return [value]
    if isinstance(value, list):
        return [item for member in value for item in _json_strings(member)]
    if isinstance(value, dict):
        return [item for key, member in value.items()
                for item in _json_strings(key) + _json_strings(member)]
    return []


def _privacy_scan(config: Config, path: Path, raw: bytes) -> None:
    require(b"\0" not in raw, "NUL byte in inspectable package file")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise VerificationError("non-UTF-8 inspectable package file") from exc
    tokens = _policy_tokens(config)
    relative = path.relative_to(config.root).as_posix() if path.is_relative_to(config.root) else path.name
    components = relative.split(chr(47))
    require(not any(token in component or token in text for token in tokens for component in components), "forbidden public token")
    if path.suffix == ".json":
        strings = _json_strings(_inspectable_json(text))
        require(not any("\0" in value for value in strings), "NUL byte in inspectable JSON string")
        require(not any(token in value for token in tokens for value in strings), "forbidden public token")
        require(not any(has_absolute_host_path(value) for value in strings), "absolute host path")
        return
    path_text = text
    if path.suffix == ".lean":
        path_text = _mask_lean_comment_delimiters(text)
    require(not has_absolute_host_path(path_text), "absolute host path")


def _read_relocated_bytes(config: Config, path: Path, expected_sha256: str,
                          expected_bytes: int, label: str) -> bytes:
    try:
        mode = path.lstat().st_mode
    except OSError as exc:
        raise VerificationError(label + " changed") from exc
    require(not path.is_symlink() and stat.S_ISREG(mode), label + " changed")
    try:
        raw = path.read_bytes()
    except OSError as exc:
        raise VerificationError(label + " changed") from exc
    require(len(raw) == expected_bytes and
            hashlib.sha256(raw).hexdigest() == expected_sha256, label + " changed")
    _privacy_scan(config, path, raw)
    return raw


def _read_relocated_input(config: Config, path: Path, expected_sha256: str,
                          expected_bytes: int, label: str) -> str:
    raw = _read_relocated_bytes(config, path, expected_sha256, expected_bytes, label)
    try:
        return raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise VerificationError(label + " is not UTF-8") from exc


def _check_relocated_input(config: Config, path: Path, expected_sha256: str,
                           expected_bytes: int, label: str) -> None:
    _read_relocated_input(config, path, expected_sha256, expected_bytes, label)


def _mask_lean_comment_delimiters(text: str) -> str:
    result = list(text)
    depth, index, quoted, line_comment = 0, 0, False, False

    def reviewed_opener(at: int) -> int:
        if not text.startswith(chr(47) + "-", at):
            return 0
        width = 3 if at + 2 < len(text) and text[at + 2] in ("-", "!") else 2
        return width if at + width < len(text) and text[at + width].isspace() else 0

    while index < len(text):
        if line_comment:
            if text[index] == "\n":
                line_comment = False
            index += 1
            continue
        if quoted:
            if text[index] == "\\":
                index += 2
                continue
            if text[index] == '"':
                quoted = False
            index += 1
            continue
        if depth and text.startswith("-" + chr(47), index):
            result[index:index + 2] = "  "; depth -= 1; index += 2; continue
        opener = reviewed_opener(index)
        if opener:
            result[index:index + opener] = " " * opener; depth += 1; index += opener; continue
        if not depth and text.startswith("--", index):
            line_comment = True; index += 2; continue
        if not depth and text[index] == '"':
            quoted = True
        index += 1
    return "".join(result)


def _ancestor_directories(relative_paths: set[str]) -> set[str]:
    """Return every non-root directory implied by normalized file paths."""
    result: set[str] = set()
    for relative in relative_paths:
        parts = relative.split(chr(47))
        require(all(parts) and all(part not in (".", "..") for part in parts), "invalid expected path")
        result.update(chr(47).join(parts[:index]) for index in range(1, len(parts)))
    return result


def _snapshot_public_inputs(config: Config) -> list[dict[str, Any]]:
    """Read every public member and reject additions, aliases, and later drift."""
    expected = {"package.json"} | {path for path, _, _ in config.public_files}
    table = {path: (digest, size) for path, digest, size in config.public_files}
    require(len(table) == len(config.public_files), "duplicate public input binding")
    found: set[str] = set()
    directories: set[str] = set()
    folded: set[str] = set()
    members: list[dict[str, Any]] = []
    for path in config.root.rglob("*"):
        relative = path.relative_to(config.root).as_posix()
        mode = path.lstat().st_mode
        require(not path.is_symlink(), "symlink in package")
        require(path.is_dir() or stat.S_ISREG(mode), "invalid public tree member")
        require(relative.casefold() not in folded, "case-fold collision in public tree")
        folded.add(relative.casefold())
        if path.is_dir():
            directories.add(relative)
            require(not any(token in component for token in _policy_tokens(config) for component in relative.split(chr(47))),
                    "forbidden public token")
            continue
        if path.suffix in OBJECT_SUFFIXES or path.suffix in (".pyc", ".zip", ".tar", ".gz") or path.name.startswith("receipt") or \
                "crosswalk" in path.name.lower() or "__pycache__" in path.parts or ".lake" in path.parts:
            raise VerificationError("historical build object")
        found.add(relative)
        require(relative in expected, "unbound public package member")
        raw = path.read_bytes()
        _privacy_scan(config, path, raw)
        digest, size = hashlib.sha256(raw).hexdigest(), len(raw)
        if relative == "package.json":
            require(digest == config.package_sha256, "package configuration changed")
        else:
            expected_digest, expected_size = table[relative]
            require(digest == expected_digest and size == expected_size, "public input hash mismatch")
        members.append({"path": "@package/" + relative, "sha256": digest, "bytes": size})
    require(found == expected, "public input tree differs from binding")
    expected_dirs = _ancestor_directories(expected)
    require(directories == expected_dirs, "public input directory topology differs")
    return sorted(members, key=lambda item: item["path"])


def _compiled_privacy_scan(config: Config, path: Path, env: dict[str, str]) -> None:
    try:
        mode = path.lstat().st_mode
    except OSError as exc:
        raise VerificationError("compiled object changed") from exc
    require(not path.is_symlink() and stat.S_ISREG(mode), "compiled object changed")
    try:
        raw = path.read_bytes()
    except OSError as exc:
        raise VerificationError("compiled object changed") from exc
    tokens = _policy_tokens(config)
    require(not any(token.encode("utf-8") in raw for token in tokens), "forbidden public token in compiled object")
    require(not has_compiled_host_path(raw),
            "absolute host path in compiled object")
    try:
        strings = _helper("strings")
    except VerificationError as exc:
        raise VerificationError("compiled strings helper is unavailable") from exc
    try:
        output = _run([str(strings), "-a", str(path)], path.parent, env)
    except VerificationError as exc:
        raise VerificationError("compiled strings scan failed") from exc
    require(not any(token in output for token in tokens),
            "forbidden public token in compiled object strings output")
    require(not has_compiled_host_path(output.encode("utf-8")),
            "absolute host path in compiled object strings output")


def _discover_declarations(clean: str, owner: str) -> set[tuple[str, str]]:
    """Parse the deliberately small reviewed command grammar line by line."""
    stack: list[tuple[str, str | None]] = []
    active: str | None = None
    result: set[tuple[str, str]] = set()
    pending_omit = False
    blocked = re.compile(
        REGEX_WORD_BOUNDARY + r"(?:alias|axiom|builtin_initialize|class|command|constant|declare_syntax_cat|deriving|elab|elab_rules|"
        r"example|export|extern|include|inductive|infix|infixl|infixr|initialize|instance|irreducible_def|lemma|macro|macro_rules|mutual|notation|opaque|"
        r"partial|postfix|prefix|private|protected|structure|syntax|universe|where)" + REGEX_WORD_BOUNDARY +
        "|" + REGEX_WORD_BOUNDARY + r"let\s+rec" + REGEX_WORD_BOUNDARY)
    for raw in clean.splitlines():
        line = raw.strip()
        if not line:
            continue
        if re.search(REGEX_WORD_BOUNDARY + "set_option" + REGEX_WORD_BOUNDARY, line):
            require(line == "set_option autoImplicit false" and not stack and not pending_omit,
                    "unsupported declaration-generating command")
            continue
        if re.search(REGEX_WORD_BOUNDARY + "omit" + REGEX_WORD_BOUNDARY, line):
            require(line == "omit [Fintype ι] in" and active == OWNER_BY_MODULE[owner] and not pending_omit,
                    "unsupported declaration-generating command")
            pending_omit = True
            continue
        require(blocked.search(line) is None, "unsupported declaration-generating command")
        require(not line.startswith("@["), "unsupported declaration attribute")
        if pending_omit:
            require(re.match(r"theorem\s+[A-Za-z_][A-Za-z_0-9']*\b", line) is not None,
                    "unsupported declaration-generating command")
        opened = re.fullmatch(r"namespace\s+([A-Za-z_][A-Za-z_0-9.']*)", line)
        if opened:
            require(not pending_omit, "unsupported declaration-generating command")
            name = opened.group(1)
            require(name == ROOT_NAMESPACE or name.startswith(ROOT_NAMESPACE + "."), "wrong namespace")
            stack.append(("namespace", name))
            active = name
            continue
        section = re.fullmatch(r"(?:noncomputable\s+)?section(?:\s+([A-Za-z_][A-Za-z_0-9']*))?", line)
        if section:
            require(not pending_omit, "unsupported declaration-generating command")
            stack.append(("section", section.group(1)))
            continue
        ended = re.fullmatch(r"end(?:\s+([A-Za-z_][A-Za-z_0-9.']*))?", line)
        if ended:
            require(not pending_omit, "unsupported declaration-generating command")
            require(stack, "unmatched end command")
            kind, name = stack.pop()
            given = ended.group(1)
            require(given is None or given == name, "mismatched end command")
            active = next((item for kind, item in reversed(stack) if kind == "namespace"), None)
            continue
        declared = re.match(r"(?:noncomputable\s+)?(def|abbrev|theorem)\s+([A-Za-z_][A-Za-z_0-9']*)\b", line)
        if declared:
            require(active == OWNER_BY_MODULE[owner], "declaration owner differs from reviewed module")
            require(not pending_omit or declared.group(1) == "theorem", "unsupported declaration-generating command")
            result.add((active + "." + declared.group(2), declared.group(1)))
            pending_omit = False
        elif re.search(REGEX_WORD_BOUNDARY + r"(?:def|abbrev|theorem)" + REGEX_WORD_BOUNDARY, line):
            raise VerificationError("unsupported declaration-generating command")
    require(not pending_omit, "unsupported declaration-generating command")
    require(not stack, "unclosed namespace or section")
    return result


def preflight(config: Config) -> list[str]:
    require(config.root.is_dir(), "missing package root")
    _snapshot_public_inputs(config)
    module_paths = {item.source for item in config.modules}
    allowed_paths = module_paths | {config.facade} | {item.source for item in config.controls} | {"package.json"}
    for path in config.root.rglob("*"):
        if path.is_symlink():
            raise VerificationError("symlink in package")
        mode = path.stat(follow_symlinks=False).st_mode
        require(path.is_dir() or stat.S_ISREG(mode), "special filesystem entry in package")
        if path.is_file():
            if path.suffix in OBJECT_SUFFIXES or path.suffix in (".pyc", ".zip", ".tar", ".gz") or path.name.startswith("receipt") or "crosswalk" in path.name.lower() or \
                    "__pycache__" in path.parts or ".lake" in path.parts:
                raise VerificationError("historical build object")
            relative = path.relative_to(config.root).as_posix()
            if path.suffix == ".lean" and relative not in allowed_paths:
                raise VerificationError("extra local Lean module")
            _privacy_scan(config, path, path.read_bytes())
    graph: dict[str, list[str]] = {}
    discovered: set[tuple[str, str, str]] = set()
    for item in config.modules:
        path = _package_file(config, item.source)
        raw = path.read_bytes()
        require(sha256_file(path) == item.sha256 and path.stat().st_size == item.bytes, "source hash mismatch")
        _privacy_scan(config, path, raw)
        try:
            clean = scan_lean(raw.decode("utf-8-sig"))
            actual = parse_imports(raw.decode("utf-8-sig"))
        except ValueError as exc:
            raise VerificationError(str(exc)) from exc
        discovered.update((item.name, name, kind) for name, kind in _discover_declarations(clean, item.name))
        require(tuple(actual) == item.imports, "declared imports differ from source")
        require(all(value in MODULES or is_external(value) for value in actual), "unlisted local import")
        graph[item.name] = actual
    facade = _package_file(config, config.facade)
    require(sha256_file(facade) == config.facade_sha256 and facade.stat().st_size == config.facade_bytes,
            "facade hash mismatch")
    try:
        facade_imports = parse_imports(facade.read_text(encoding="utf-8-sig"))
    except ValueError as exc:
        raise VerificationError(str(exc)) from exc
    require(tuple(facade_imports) == ENTRIES, "facade imports must be exact entry modules")
    try:
        facade_clean = scan_lean(facade.read_text(encoding="utf-8-sig"))
    except ValueError as exc:
        raise VerificationError(str(exc)) from exc
    require(re.sub(r"^\s*import\s+[^\n]+$", "", facade_clean, flags=re.MULTILINE).strip() == "",
            "facade must be declaration-free")
    for control in config.controls:
        path = _package_file(config, control.source)
        require(sha256_file(path) == control.sha256, "control source hash mismatch")
        try:
            imports = parse_imports(path.read_text(encoding="utf-8-sig"))
        except ValueError as exc:
            raise VerificationError(str(exc)) from exc
        require(all(value in MODULES or is_external(value) for value in imports), "control has unlisted local import")
    try:
        order = topo_sort(graph, list(config.entries))
    except ValueError as exc:
        raise VerificationError(str(exc)) from exc
    require(set(order) == set(MODULES) and tuple(order) == BUILD_ORDER, "entries do not close over exact module allowlist")
    selected = {(item.module, item.name, item.kind) for item in config.declarations}
    require(discovered == selected, "source declaration set differs from exact audit selection")
    return order


def _run(argv: list[str], cwd: Path, env: dict[str, str], expect_failure: bool = False,
         input_text: str | None = None) -> str:
    try:
        process = subprocess.run(argv, cwd=cwd, env=env, input=input_text, text=True, encoding="utf-8",
            errors="strict", stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
    except (OSError, UnicodeDecodeError, subprocess.TimeoutExpired) as exc:
        raise VerificationError("subprocess execution failed") from exc
    if (process.returncode != 0) != expect_failure:
        raise VerificationError("subprocess exit behavior differs from required control")
    return process.stdout


def _guard_compiler(lean: Path, evidence: dict[str, Any], phase: str) -> None:
    require(isinstance(evidence, dict) and set(evidence) == {"sha256", "bytes"} and
            _sha(evidence.get("sha256")) and type(evidence.get("bytes")) is int and evidence["bytes"] > 0,
            "compiler evidence is incomplete")
    try:
        mode = lean.lstat().st_mode
    except OSError as exc:
        raise VerificationError("compiler changed " + phase) from exc
    require(not lean.is_symlink() and stat.S_ISREG(mode), "compiler changed " + phase)
    try:
        digest, size = sha256_file(lean), lean.stat().st_size
    except OSError as exc:
        raise VerificationError("compiler changed " + phase) from exc
    require(digest == evidence["sha256"] and size == evidence["bytes"],
            "compiler changed " + phase)


def _run_lean(lean: Path, evidence: dict[str, Any], argv: list[str], cwd: Path,
              env: dict[str, str], expect_failure: bool = False, input_text: str | None = None) -> str:
    _guard_compiler(lean, evidence, "before invocation")
    try:
        return _run([str(lean), *argv], cwd, env, expect_failure=expect_failure, input_text=input_text)
    finally:
        _guard_compiler(lean, evidence, "after invocation")


def _helper(name: str) -> Path:
    candidate = shutil.which(name, path=os.defpath)
    require(candidate is not None, "trusted helper is unavailable")
    path = Path(candidate).resolve()
    require(path.is_file() and stat.S_ISREG(path.stat().st_mode), "trusted helper is not a regular file")
    return path


def _dependency_caches(mathlib: Path, git: Path, cwd: Path, env: dict[str, str]) -> tuple[list[tuple[str, Path]], dict[str, str]]:
    manifest = mathlib / "lake-manifest.json"
    require(sha256_file(manifest) == MATHLIB_MANIFEST_SHA256, "Mathlib manifest hash differs")
    raw = _json(manifest)
    require(set(raw) == {"version", "name", "lakeDir", "packagesDir", "packages"} and raw.get("version") == "1.1.0" and
            raw.get("name") == "mathlib" and raw.get("lakeDir") == ".lake" and raw.get("packagesDir") == ".lake/packages",
            "Mathlib manifest schema differs")
    rows = raw.get("packages")
    try:
        safe_relative(raw["packagesDir"])
    except ValueError as exc:
        raise VerificationError("Mathlib manifest schema differs") from exc
    require(isinstance(rows, list) and len(rows) == len(DEPENDENCY_PINS), "Mathlib dependency manifest differs")
    seen: set[str] = set()
    caches: list[tuple[str, Path]] = []
    revisions: dict[str, str] = {}
    for expected_name, row in zip(DEPENDENCY_ORDER, rows):
        require(isinstance(row, dict) and set(row) == {"url", "type", "subDir", "scope", "rev", "name", "inputRev", "inherited", "manifestFile", "configFile"},
                "invalid dependency row")
        name, revision = row["name"], row["rev"]
        require(name == expected_name and name not in seen and row["type"] == "git" and revision == DEPENDENCY_PINS[name],
                "dependency pin differs")
        url, scope, input_rev, inherited, config_file = DEPENDENCY_ROWS[name]
        require(row == {"url": url, "type": "git", "subDir": None, "scope": scope, "rev": revision, "name": name,
                        "inputRev": input_rev, "inherited": inherited, "manifestFile": "lake-manifest.json", "configFile": config_file},
                "dependency manifest row differs")
        seen.add(name)
        checkout = (mathlib / raw["packagesDir"] / name).resolve()
        require(checkout.is_dir() and checkout.is_relative_to(mathlib.resolve()), "dependency checkout missing")
        require(_run([str(git), "-C", str(checkout), "cat-file", "-e", revision + "^{commit}"], cwd, env) == "", "dependency revision is not a commit")
        require(_run([str(git), "-C", str(checkout), "rev-parse", "HEAD"], cwd, env).strip() == revision, "dependency checkout revision differs")
        require(_run([str(git), "-C", str(checkout), "diff", "--exit-code", "HEAD", "--", "*.lean", "lake-manifest.json"], cwd, env) == "", "dependency checkout is dirty")
        cache = checkout / ".lake" / "build" / "lib" / "lean"
        require(cache.is_dir() and not cache.is_symlink(), "dependency cache missing")
        caches.append(("@dependency/" + name, cache))
        revisions[name] = revision
    require(seen == set(DEPENDENCY_PINS), "dependency set differs")
    return caches, revisions


def _negative(argv: list[str], cwd: Path, env: dict[str, str], input_text: str | None = None) -> tuple[int, str]:
    try:
        process = subprocess.run(argv, cwd=cwd, env=env, input=input_text, text=True, encoding="utf-8",
            errors="strict", stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
    except (OSError, UnicodeDecodeError, subprocess.TimeoutExpired) as exc:
        raise VerificationError("negative control execution failed") from exc
    return process.returncode, process.stdout


def _negative_lean(lean: Path, evidence: dict[str, Any], argv: list[str], cwd: Path,
                   env: dict[str, str], input_text: str | None = None) -> tuple[int, str]:
    _guard_compiler(lean, evidence, "before invocation")
    try:
        return _negative([str(lean), *argv], cwd, env, input_text=input_text)
    finally:
        _guard_compiler(lean, evidence, "after invocation")


def _stdin_source_name(source: Path, cwd: Path) -> str:
    require(source.is_relative_to(cwd), "compiler source is not neutral")
    relative = source.relative_to(cwd).as_posix()
    try:
        safe_relative(relative)
    except ValueError as exc:
        raise VerificationError("compiler source is not neutral") from exc
    require(relative.startswith("source/") and relative != "source", "compiler source root differs")
    return relative


def _run_bound_lean(config: Config, lean: Path, compiler_evidence: dict[str, Any], source: Path,
                    expected_sha256: str, expected_bytes: int, label: str, argv: list[str],
                    cwd: Path, env: dict[str, str]) -> str:
    source_name = _stdin_source_name(source, cwd)
    input_text = _read_relocated_input(config, source, expected_sha256, expected_bytes, label)
    try:
        return _run_lean(lean, compiler_evidence,
            [*argv, "--root=source", "--stdin", source_name], cwd, env, input_text=input_text)
    finally:
        _check_relocated_input(config, source, expected_sha256, expected_bytes, label)


def _run_fifo_lean(config: Config, lean: Path, compiler_evidence: dict[str, Any], source: Path,
                   expected_sha256: str, expected_bytes: int, label: str, argv: list[str],
                   cwd: Path, env: dict[str, str]) -> str:
    """Compile checked bytes through a private neutral-path named FIFO."""
    source_name = _stdin_source_name(source, cwd)
    raw = _read_relocated_bytes(config, source, expected_sha256, expected_bytes, label)
    feed_root = cwd / "feed"
    try:
        feed_root.lstat()
    except FileNotFoundError:
        pass
    except OSError as exc:
        raise VerificationError("named FIFO feed is unavailable") from exc
    else:
        raise VerificationError("named FIFO feed must be fresh")
    fifo = feed_root / source_name.removeprefix("source/")
    created = False
    fifo_identity: tuple[int, int] | None = None
    writer: threading.Thread | None = None
    writer_started = False
    cancelled = threading.Event()
    state: dict[str, Any] = {"bytes": 0, "connected": False, "error": None}
    transcript: str | None = None
    primary: BaseException | None = None
    secondary: list[BaseException] = []
    invoked = False
    try:
        feed_root.mkdir(mode=0o700)
        require(feed_root.stat().st_mode & 0o077 == 0, "named FIFO feed is not private")
        fifo.parent.mkdir(parents=True)
        try:
            os.mkfifo(fifo, 0o600)
        except (AttributeError, NotImplementedError, OSError) as exc:
            raise VerificationError("named FIFO support is unavailable") from exc
        created = True
        fifo_stat = fifo.lstat()
        fifo_identity = (fifo_stat.st_dev, fifo_stat.st_ino)
        require(stat.S_ISFIFO(fifo_stat.st_mode) and fifo_stat.st_mode & 0o777 == 0o600,
                "named FIFO creation failed")

        def stream() -> None:
            descriptor: int | None = None
            try:
                while not cancelled.is_set():
                    try:
                        flags = os.O_WRONLY | os.O_NONBLOCK | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
                        descriptor = os.open(fifo, flags)
                        break
                    except OSError as exc:
                        if exc.errno not in (errno.ENXIO, errno.ENOENT, errno.EINTR):
                            raise
                        cancelled.wait(0.01)
                if descriptor is None:
                    return
                opened = os.fstat(descriptor)
                require(stat.S_ISFIFO(opened.st_mode) and opened.st_mode & 0o777 == 0o600 and
                        (opened.st_dev, opened.st_ino) == fifo_identity,
                        "named FIFO changed before delivery")
                state["connected"] = True
                while state["bytes"] < len(raw) and not cancelled.is_set():
                    try:
                        written = os.write(descriptor, raw[state["bytes"]:])
                    except InterruptedError:
                        continue
                    except BlockingIOError:
                        cancelled.wait(0.01)
                        continue
                    require(written > 0, "named FIFO delivery stalled")
                    state["bytes"] += written
            except Exception as exc:  # The trusted runtime reports writer failure to the main thread.
                state["error"] = exc
            finally:
                if descriptor is not None:
                    try:
                        os.close(descriptor)
                    except OSError as exc:
                        state["error"] = state["error"] or exc

        writer = threading.Thread(target=stream, name="lean-source-feed", daemon=True)
        writer.start()
        writer_started = True
        invoked = True
        transcript = _run_lean(lean, compiler_evidence,
            [*argv, "--root=feed", "feed/" + source_name.removeprefix("source/")], cwd, env)
    except BaseException as exc:
        primary = exc
    finally:
        cancelled.set()
        if writer is not None and writer_started:
            writer.join(timeout=2)
            if writer.is_alive():
                secondary.append(VerificationError("named FIFO writer did not stop"))
        if invoked and (state["error"] is not None or state["connected"] is not True or
                        state["bytes"] != len(raw)):
            secondary.append(VerificationError("named FIFO delivery was incomplete"))
        if created:
            try:
                final_fifo = fifo.lstat()
                if not stat.S_ISFIFO(final_fifo.st_mode) or final_fifo.st_mode & 0o777 != 0o600 or \
                        fifo_identity is None or \
                        (final_fifo.st_dev, final_fifo.st_ino) != fifo_identity:
                    secondary.append(VerificationError("named FIFO changed during compilation"))
                else:
                    fifo.unlink()
            except FileNotFoundError as exc:
                secondary.append(VerificationError("named FIFO disappeared during compilation"))
            except OSError as exc:
                secondary.append(VerificationError("named FIFO cleanup failed"))
        for directory in (fifo.parent, feed_root):
            try:
                directory.rmdir()
            except FileNotFoundError:
                pass
            except OSError as exc:
                if directory == feed_root:
                    secondary.append(VerificationError("named FIFO feed cleanup failed"))
        try:
            _check_relocated_input(config, source, expected_sha256, expected_bytes, label)
        except BaseException as exc:
            secondary.append(exc)
    if primary is not None:
        for problem in secondary:
            add_exception_note(primary, "secondary FIFO failure: " + str(problem))
        raise primary
    if secondary:
        raise secondary[0]
    require(transcript is not None, "named FIFO compiler did not run")
    return transcript


def _negative_bound_lean(config: Config, lean: Path, compiler_evidence: dict[str, Any], source: Path,
                         expected_sha256: str, expected_bytes: int, label: str, argv: list[str],
                         cwd: Path, env: dict[str, str]) -> tuple[int, str]:
    source_name = _stdin_source_name(source, cwd)
    input_text = _read_relocated_input(config, source, expected_sha256, expected_bytes, label)
    try:
        return _negative_lean(lean, compiler_evidence,
            [*argv, "--root=source", "--stdin", source_name], cwd, env, input_text=input_text)
    finally:
        _check_relocated_input(config, source, expected_sha256, expected_bytes, label)


def _check_deps(lean: Path, compiler_evidence: dict[str, Any], config: Config, source: Path,
                expected_sha256: str, expected_bytes: int, label: str, cwd: Path,
                env: dict[str, str], build: Path,
                external: tuple[tuple[str, Path], ...]) -> dict[str, tuple[str, Path]]:
    transcript = _run_bound_lean(config, lean, compiler_evidence, source, expected_sha256,
        expected_bytes, label, ["--deps"], cwd, env)
    rows = [line.strip() for line in transcript.splitlines() if line.strip()]
    require(rows, "compiler dependency output is empty")
    hashes: dict[str, tuple[str, Path]] = {}
    by_relative: dict[str, str] = {}
    roots = (("@run/build", build), *external)
    for logical_root, root in roots:
        require(logical_root.startswith("@") and root.is_dir(), "invalid dependency search root")
        for candidate in root.rglob("*.olean"):
            mode = candidate.lstat().st_mode
            require(not candidate.is_symlink() and stat.S_ISREG(mode), "invalid dependency object")
            relative = candidate.relative_to(root).as_posix()
            logical = logical_root + chr(47) + relative
            prior = by_relative.setdefault(relative.casefold(), logical)
            require(prior == logical, "case-fold collision in dependency objects")
    for row in rows:
        reported = Path(row)
        path = (reported if reported.is_absolute() else cwd / reported).resolve()
        require(path.is_file() and path.suffix == ".olean", "malformed compiler dependency output")
        identities = [(logical_root, root) for logical_root, root in roots if path.is_relative_to(root)]
        require(len(identities) == 1, "compiler dependency resolved outside trusted roots")
        logical_root, root = identities[0]
        logical = logical_root + chr(47) + path.relative_to(root).as_posix()
        value = (sha256_file(path), path)
        require(logical not in hashes, "duplicate compiler dependency output")
        hashes[logical] = value
    return hashes


def validate_audit(config: Config, audit: dict[str, tuple[str, list[str]]]) -> None:
    expected = {item.name for item in config.declarations}
    require(set(audit) == expected and len(audit) == 203, "declaration audit is incomplete")
    for name, (literal_type, axioms) in audit.items():
        require(isinstance(literal_type, str) and literal_type.strip(), "literal type missing: " + name)
        require(set(axioms) <= ALLOWED_AXIOMS, "disallowed axiom: " + name)
    if config.kind_totals is not None:
        actual = {kind: sum(item.kind == kind for item in config.declarations) for kind in config.kind_totals}
        require(actual == config.kind_totals, "declaration kind totals differ")


def parse_audit(config: Config, output: str) -> dict[str, tuple[str, list[str]]]:
    result: dict[str, tuple[str, list[str]]] = {}
    cursor = 0
    def marker(tag: str, name: str, at: int, phase_body: bool = False) -> tuple[int, int]:
        matched = re.search(r'^[ \t]*"__AUDIT_' + tag + " " + re.escape(name) +
                            r'"[ \t]*:[ \t]*String[ \t]*(?:\n|\Z)', output[at:], re.MULTILINE)
        require(matched is not None, "framed audit record missing or out of order: " + name)
        start, end = at + matched.start(), at + matched.end()
        preceding = output[at:start]
        if phase_body:
            require("__AUDIT_" not in preceding, "audit phase contains an unexpected marker: " + name)
        else:
            require(not preceding.strip(), "audit records are out of order: " + name)
        return start, end
    identifier = r"[A-Za-z_][A-Za-z0-9_']*"
    universe = "(?:" + re.escape(".{") + r"\s*" + identifier + "(?:" + r"\s*" + "," + r"\s*" + \
        identifier + ")*" + r"\s*" + re.escape("}") + ")?"
    for declaration in config.declarations:
        name = declaration.name
        _, cursor = marker("BEGIN", name, cursor)
        kind_end_start, kind_end_end = marker("KIND_END", name, cursor, phase_body=True)
        kind_body = output[cursor:kind_end_start]
        printed = re.fullmatch(r"(?:@\[reducible\]\s+)?(?:noncomputable\s+)?(theorem|def|abbrev)\s+" + re.escape(name) + universe + r"(?:\s|:|$)[\s\S]*", kind_body.strip())
        require(printed is not None, "environment declaration kind evidence is missing: " + name)
        reducible = kind_body.lstrip().startswith("@[reducible]")
        require(not reducible or printed.group(1) == "def", "environment declaration kind evidence is invalid: " + name)
        actual_kind = "abbrev" if reducible else printed.group(1)
        require(actual_kind == declaration.kind, "environment declaration kind differs: " + name)
        cursor = kind_end_end
        type_end_start, type_end_end = marker("TYPE_END", name, cursor, phase_body=True)
        type_body = output[cursor:type_end_start]
        header = re.match(r"\s*@?" + re.escape(name) + universe + r"\s*:\s*", type_body)
        require(header is not None, "literal type audit missing: " + name)
        literal_type = type_body[header.end():].strip()
        require(literal_type, "literal type missing: " + name)
        cursor = type_end_end
        axiom_end_start, axiom_end_end = marker("AXIOM_END", name, cursor, phase_body=True)
        axiom_body = output[cursor:axiom_end_start].strip()
        axiom = re.fullmatch(r"'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", axiom_body)
        no_axiom = re.fullmatch(r"'" + re.escape(name) + r"' does not depend on any axioms", axiom_body)
        require((axiom is not None) ^ (no_axiom is not None), "transitive axiom audit missing or ambiguous: " + name)
        axioms = [] if no_axiom else [item.strip() for item in axiom.group(1).split(",") if item.strip()]
        require(len(axioms) == len(set(axioms)), "duplicate transitive axiom: " + name)
        result[name] = (literal_type, sorted(axioms))
        cursor = axiom_end_end
        _, cursor = marker("END", name, cursor)
    require(not output[cursor:].strip(), "unparsed audit output")
    validate_audit(config, result)
    return result


def validate_control(name: str, exit_code: int, output: str, markers: tuple[str, ...]) -> dict[str, str]:
    """Accept one pinned Lean 4.19 type-mismatch diagnostic, not generic failure."""
    require(exit_code == 1, "negative control unexpectedly succeeded or crashed")
    require(name in CONTROL_DIGESTS and re.fullmatch(r"[^\n:]+\.lean:\d+:\d+: error: type mismatch\n(?:[^\n]+\n){5}", output) is not None,
            "negative control diagnostic class differs: " + name)
    lines = output.splitlines()
    require(all(marker in output for marker in markers), "negative control diagnostic marker missing: " + name)
    require(not any(item in output.lower() for item in ("unknown module", "unknown identifier", "object file", "no such file", "syntax error", "unexpected token", "panic", "segmentation", "unsolved goals", "warning:")),
            "negative control failed outside mathematics: " + name)
    normalized = re.sub(r"^[^\n:]+\.lean:\d+:\d+:", "<file>:", output)
    digest = hashlib.sha256(normalized.encode("utf-8")).hexdigest()
    require(digest == CONTROL_DIGESTS[name], "negative control transcript differs: " + name)
    return {"status": "PASS", "diagnostic_class": "lean-4.19-type-mismatch", "normalized_sha256": digest}


def _logical(config: Config, value: Path | str, lean: Path | None = None, mathlib: Path | None = None) -> str:
    path = Path(value).resolve()
    if path == config.root.resolve():
        return "@package"
    if path.is_relative_to(config.root.resolve()):
        return "@package/" + path.relative_to(config.root.resolve()).as_posix()
    if lean is not None and path == lean.resolve():
        return "@lean"
    if mathlib is not None and path == mathlib.resolve():
        return "@mathlib"
    raise VerificationError("unrecognized logical path")


def _canonical(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii") + b"\n"


def _certificate_strings(value: Any) -> list[str]:
    if isinstance(value, str):
        return [value]
    if isinstance(value, list):
        return [item for member in value for item in _certificate_strings(member)]
    if isinstance(value, dict):
        return [item for key, member in value.items() for item in _certificate_strings(key) + _certificate_strings(member)]
    return []


def _certificate_string_fields(
    value: Any, location: tuple[Any, ...] = (), dictionary_key: bool = False
) -> list[tuple[str, bool]]:
    """Retain enough field context to distinguish Lean literals from paths."""
    if isinstance(value, str):
        literal_type = (not dictionary_key and len(location) == 2 and
                        location[0] == "literal_types" and isinstance(location[1], str))
        return [(value, literal_type)]
    if isinstance(value, list):
        return [item for index, member in enumerate(value)
                for item in _certificate_string_fields(member, (*location, index))]
    if isinstance(value, dict):
        return [item for key, member in value.items()
                for item in (_certificate_string_fields(key, (*location, key), True) +
                             _certificate_string_fields(member, (*location, key)))]
    return []


def _validate_certificate_paths(document: dict[str, Any]) -> None:
    for value, literal_type in _certificate_string_fields(document):
        schemes = [match.group(0) for match in re.finditer(r"(?<![A-Za-z0-9+.-])[A-Za-z][A-Za-z0-9+.-]*:(?=\S)", value)]
        require("\0" not in value and "\\" not in value and all(scheme.lower() in ("http:", "https:") for scheme in schemes) and not re.match(r"^[A-Za-z][A-Za-z0-9+.-]*:", value) and
                not value.startswith(chr(47)) and not has_absolute_host_path(value) and not re.match(r"^[A-Za-z]:", value),
                "certificate contains nonlogical path")
        first_token = value.split(maxsplit=1)[0] if value else ""
        if first_token.startswith("@") and (not literal_type or chr(47) in first_token):
            bases = ("@package", "@run", "@lean", "@mathlib")
            tail: str | None = None
            if value in bases:
                continue
            for base in bases:
                if value.startswith(base + chr(47)):
                    tail = value.removeprefix(base + chr(47))
                    break
            if tail is None and value.startswith("@dependency/"):
                remainder = value.removeprefix("@dependency/")
                dependency, separator, dependency_tail = remainder.partition(chr(47))
                require(dependency in DEPENDENCY_PINS, "certificate contains unknown logical path")
                if not separator:
                    continue
                tail = dependency_tail
            require(tail is not None, "certificate contains unknown logical path")
            try:
                safe_relative(tail)
            except ValueError as exc:
                raise VerificationError("certificate contains invalid logical path") from exc


def _expected_objects() -> set[str]:
    return {"@run/build/" + Path(local_source_path(module)).with_suffix(".olean").as_posix() for module in MODULES}


def _validate_build_tree(root: Path, objects: dict[str, str]) -> None:
    require(set(objects) == _expected_objects() and all(_sha(value) for value in objects.values()),
            "fresh object keys differ from exact build contract")
    found: set[str] = set()
    directories: set[str] = set()
    folded: set[str] = set()
    for path in root.rglob("*"):
        relative = path.relative_to(root).as_posix()
        mode = path.lstat().st_mode
        require(not path.is_symlink() and (path.is_dir() or stat.S_ISREG(mode)), "invalid fresh build member")
        require(relative.casefold() not in folded, "case-fold collision in fresh build")
        folded.add(relative.casefold())
        if path.is_dir():
            directories.add(relative)
        else:
            found.add("@run/build/" + relative)
    require(found == _expected_objects(), "fresh build tree has missing or extra members")
    expected_dirs = _ancestor_directories({logical.removeprefix("@run/build/") for logical in _expected_objects()})
    require(directories == expected_dirs, "fresh build directory topology differs")
    for logical, digest in objects.items():
        copied = root / logical.removeprefix("@run/build/")
        require(copied.is_file() and sha256_file(copied) == digest, "fresh object preservation mismatch")


def _validate_final_stage(stage: Path, config: Config, objects: dict[str, str], artifact: dict[str, Any],
                          documents: dict[str, dict[str, Any]]) -> None:
    expected_files = {"types-and-axioms.txt"} | {"certificates/" + name for name in CERTIFICATES}
    expected_files |= {"build/" + key.removeprefix("@run/build/") for key in objects}
    expected_dirs = _ancestor_directories(expected_files)
    files: set[str] = set()
    directories: set[str] = set()
    folded: set[str] = set()
    for path in stage.rglob("*"):
        relative = path.relative_to(stage).as_posix()
        mode = path.lstat().st_mode
        require(not path.is_symlink() and (path.is_dir() or stat.S_ISREG(mode)), "invalid final stage member")
        require(relative.casefold() not in folded, "case-fold collision in final stage")
        folded.add(relative.casefold())
        (directories if path.is_dir() else files).add(relative)
    require(files == expected_files and directories == expected_dirs, "final stage topology differs")
    _validate_build_tree(stage / "build", objects)
    evidence = stage / "types-and-axioms.txt"
    require(evidence.stat().st_size == artifact["bytes"] and sha256_file(evidence) == artifact["sha256"],
            "type and axiom evidence changed")
    for name in CERTIFICATES:
        raw = (stage / "certificates" / name).read_bytes()
        require(raw == _canonical(documents[name]), "final certificate bytes changed")
        _validate_certificate_paths(documents[name])
        _privacy_scan(config, stage / "certificates" / name, raw)
        document = _json(stage / "certificates" / name)
        require(document.get("schema_version") == 1 and document.get("status") == "PASS", "final certificate schema differs")
    for name in ("BUILD_CERTIFICATE.json", "DECLARATION_CERTIFICATE.json", "AXIOM_CERTIFICATE.json"):
        require(_json(stage / "certificates" / name).get("type_axiom_artifact") == artifact,
                "final type artifact binding differs")
    privacy = _json(stage / "certificates" / "PRIVACY_CERTIFICATE.json")
    require(privacy.get("retained_members") == [
        *[{"path": path, "sha256": digest} for path, digest in sorted(objects.items())], artifact],
        "final retained privacy evidence differs")
    reproducibility = _json(stage / "certificates" / "REPRODUCIBILITY_CERTIFICATE.json")
    require(reproducibility.get("certificate_hashes") == {name: hashlib.sha256((stage / "certificates" / name).read_bytes()).hexdigest()
            for name in CERTIFICATES[:-1]}, "final reproducibility graph differs")


def _validate_build_evidence(build: dict[str, Any]) -> None:
    required = {"status", "lean", "mathlib", "manifest", "objects", "direct_dependencies", "dependency_revisions",
                "dependency_evidence_scope", "external_cache_boundary", "external_caches_reused", "compiler",
                "mathlib_manifest"}
    require(set(build) == required and build.get("status") == "PASS" and build.get("lean") == "@lean" and build.get("mathlib") == "@mathlib" and
            build.get("manifest") == "@mathlib/lake-manifest.json" and build.get("external_caches_reused") is True and
            build.get("dependency_evidence_scope") == "lean-direct-import-objects-only" and
            build.get("external_cache_boundary") == "pinned-checkouts-with-prebuilt-objects-reused",
            "build evidence is incomplete")
    require(isinstance(build.get("objects"), dict) and isinstance(build.get("direct_dependencies"), dict) and
            build.get("dependency_revisions") == DEPENDENCY_PINS, "build dependency evidence differs")
    _validate_build_tree_contract(build["objects"])
    external_roots: set[str] = set()
    folded: set[str] = set()
    for logical, digest in build["direct_dependencies"].items():
        require(isinstance(logical, str) and _sha(digest), "dependency logical identity differs")
        require(logical.casefold() not in folded, "dependency logical identity has a case-fold collision")
        folded.add(logical.casefold())
        if logical.startswith("@run/build/"):
            require(logical in build["objects"] and build["objects"][logical] == digest, "local dependency evidence differs")
        else:
            _validate_dependency_logical(logical)
            external_roots.add("mathlib" if logical.startswith("@mathlib/") else "lean" if logical.startswith("@lean/") else "dependency")
    require(external_roots >= {"mathlib", "lean"}, "external dependency evidence is incomplete")
    for key in ("compiler", "mathlib_manifest"):
        evidence = build.get(key)
        require(isinstance(evidence, dict) and set(evidence) == {"sha256", "bytes"} and _sha(evidence.get("sha256")) and
                type(evidence.get("bytes")) is int and evidence["bytes"] > 0, "compiler evidence is incomplete")
    require(build["mathlib_manifest"]["sha256"] == MATHLIB_MANIFEST_SHA256, "Mathlib manifest evidence differs")


def _validate_build_tree_contract(objects: dict[str, Any]) -> None:
    require(set(objects) == _expected_objects() and all(_sha(value) for value in objects.values()),
            "fresh object keys differ from exact build contract")


def _validate_dependency_logical(logical: str) -> None:
    matched = re.fullmatch(r"@(mathlib|lean|dependency" + chr(47) + r"(?:" + "|".join(re.escape(name) for name in DEPENDENCY_ORDER) + r"))" + chr(47) + r"(.*)", logical)
    require(matched is not None, "dependency logical identity differs")
    tail = matched.group(2)
    try:
        safe_relative(tail)
    except ValueError as exc:
        raise VerificationError("dependency logical identity differs") from exc
    require(tail.endswith(".olean"), "dependency logical identity differs")


def emit_certificates(result: VerificationResult, output: Path, build_directory: Path | None = None) -> list[Path]:
    _validate_build_evidence(result.build)
    public_members = _snapshot_public_inputs(result.config)
    require(sha256_file(result.config.policy) == result.config.policy_sha256,
            "authorized input changed before certificate publication")
    for item in result.config.modules:
        source = _package_file(result.config, item.source)
        require(sha256_file(source) == item.sha256 and source.stat().st_size == item.bytes, "source changed before certificate publication")
    facade = _package_file(result.config, result.config.facade)
    require(sha256_file(facade) == result.config.facade_sha256 and facade.stat().st_size == result.config.facade_bytes,
            "facade changed before certificate publication")
    for control in result.config.controls:
        require(sha256_file(_package_file(result.config, control.source)) == control.sha256,
                "control changed before certificate publication")
    validate_audit(result.config, result.audit)
    require(result.module_order == list(BUILD_ORDER), "certificate emission requires complete build order")
    require(set(result.controls) == set(CONTROL_DIGESTS) and all(isinstance(result.controls.get(name), dict) and
                set(result.controls[name]) == {"status", "diagnostic_class", "normalized_sha256"} and result.controls[name].get("status") == "PASS" and
                result.controls[name].get("diagnostic_class") == "lean-4.19-type-mismatch" and
                result.controls[name].get("normalized_sha256") == CONTROL_DIGESTS[name] for name in CONTROL_DIGESTS),
            "certificate emission requires passing negative controls")
    require(build_directory is not None, "certificate emission requires preserved fresh objects")
    output = Path(output)
    require(not output.exists(), "certificate output must be fresh")
    sources = [{"path": "@package/" + item.source, "sha256": item.sha256, "bytes": item.bytes} for item in result.config.modules]
    public_table_hash = hashlib.sha256(_canonical(public_members)).hexdigest()
    common = {"schema_version": 1, "status": "PASS", "scope": "arithmetic-clock", "inputs": sources,
              "hashes": {"package_config": result.config.package_sha256, "facade": result.config.facade_sha256,
                         "wrong_period": CONTROL_SHA256},
              "toolchain": {"lean_version": LEAN_VERSION, "lean_commit": LEAN_COMMIT, "mathlib_revision": MATHLIB_REVISION}}
    documents = {
        "SOURCE_CERTIFICATE.json": {**common, "source_count": 9, "facade": "@package/ArithmeticClock.lean",
            "public_members": public_members, "public_member_count": len(public_members), "public_member_table_sha256": public_table_hash},
        "BUILD_CERTIFICATE.json": {**common, "module_order": result.module_order, "fresh": True,
            "paths": {key: result.build[key] for key in ("lean", "mathlib", "manifest")},
            "objects": dict(sorted(result.build.get("objects", {}).items())),
            "direct_dependencies": dict(sorted(result.build.get("direct_dependencies", {}).items())),
            "dependency_revisions": dict(sorted(result.build.get("dependency_revisions", {}).items())),
            "dependency_evidence_scope": result.build.get("dependency_evidence_scope"),
            "external_cache_boundary": result.build.get("external_cache_boundary"),
            "external_caches_reused": result.build.get("external_caches_reused"),
            "compiler": result.build.get("compiler"), "mathlib_manifest": result.build.get("mathlib_manifest")},
        "DECLARATION_CERTIFICATE.json": {**common, "declaration_count": 203,
            "literal_types": {key: value[0] for key, value in sorted(result.audit.items())}},
        "AXIOM_CERTIFICATE.json": {**common, "allowed_axioms": sorted(ALLOWED_AXIOMS),
            "transitive_axioms": {key: value[1] for key, value in sorted(result.audit.items())}},
        "CONTROL_CERTIFICATE.json": {**common, "controls": dict(sorted(result.controls.items()))},
        "PRIVACY_CERTIFICATE.json": {"schema_version": 1, "status": "PASS", "scope": "arithmetic-clock", "inputs": public_members,
            "hashes": {"external_policy": result.config.policy_sha256}, "finding_count": 0,
            "member_count": len(public_members), "member_table_sha256": public_table_hash},
    }
    stage = Path(tempfile.mkdtemp(prefix="certificate-stage-", dir=output.parent))
    try:
        destination = stage / "certificates"
        destination.mkdir()
        build_directory = Path(build_directory)
        require(build_directory.is_dir() and not build_directory.is_symlink(), "fresh build directory is missing")
        expected_objects = result.build.get("objects")
        require(isinstance(expected_objects, dict), "exact fresh object evidence is required")
        _validate_build_tree(build_directory, expected_objects)
        copied_build = stage / "build"
        copied_build.mkdir()
        for logical in sorted(expected_objects):
            relative = Path(logical.removeprefix("@run/build/"))
            target = copied_build / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(build_directory / relative, target)
        _validate_build_tree(copied_build, expected_objects)
        for logical, digest in expected_objects.items():
            copied = stage / "build" / logical.removeprefix("@run/build/")
            _compiled_privacy_scan(result.config, copied, {"PATH": os.defpath, "LANG": "C", "LC_ALL": "C"})
        newline = chr(10)
        evidence = "".join("TYPE " + name + newline + literal + newline + "AXIOMS " + ",".join(axioms) + newline * 2
                           for name, (literal, axioms) in sorted(result.audit.items()))
        evidence_path = stage / "types-and-axioms.txt"
        evidence_path.write_text(evidence, encoding="utf-8", newline="\n")
        artifact = {"path": "@run/types-and-axioms.txt", "bytes": evidence_path.stat().st_size,
                    "sha256": sha256_file(evidence_path)}
        documents["PRIVACY_CERTIFICATE.json"]["retained_members"] = [
            *[{"path": path, "sha256": digest} for path, digest in sorted(expected_objects.items())], artifact]
        documents["PRIVACY_CERTIFICATE.json"]["retained_member_count"] = len(expected_objects) + 1
        documents["BUILD_CERTIFICATE.json"]["type_axiom_artifact"] = artifact
        documents["DECLARATION_CERTIFICATE.json"]["type_axiom_artifact"] = artifact
        documents["AXIOM_CERTIFICATE.json"]["type_axiom_artifact"] = artifact
        for name in CERTIFICATES[:-1]:
            document = documents[name]
            _validate_certificate_paths(document)
            (destination / name).write_bytes(_canonical(document))
        documents["REPRODUCIBILITY_CERTIFICATE.json"] = {**common, "canonical_json": True,
            "source_hashes": {item.source: item.sha256 for item in result.config.modules},
            "certificate_hashes": {name: hashlib.sha256((destination / name).read_bytes()).hexdigest() for name in CERTIFICATES[:-1]}}
        _validate_certificate_paths(documents[CERTIFICATES[-1]])
        (destination / CERTIFICATES[-1]).write_bytes(_canonical(documents[CERTIFICATES[-1]]))
        require({path.name for path in destination.iterdir()} == set(CERTIFICATES), "certificate suite is incomplete")
        for path in destination.iterdir():
            raw = path.read_bytes()
            _privacy_scan(result.config, path, raw)
            document = _json(path)
            require(set(("schema_version", "status", "scope", "inputs", "hashes")) <= set(document),
                    "certificate schema is incomplete")
        _privacy_scan(result.config, evidence_path, evidence_path.read_bytes())
        require(_snapshot_public_inputs(result.config) == public_members and sha256_file(result.config.policy) == result.config.policy_sha256,
                "public input changed during certificate publication")
        reproducibility = _json(destination / CERTIFICATES[-1])
        require(reproducibility.get("certificate_hashes") == {
            name: hashlib.sha256((destination / name).read_bytes()).hexdigest() for name in CERTIFICATES[:-1]},
            "reproducibility certificate hash graph mismatch")
        _validate_final_stage(stage, result.config, expected_objects, artifact, documents)
        os.replace(stage, output)
        stage = Path(".")
        return [output / "certificates" / name for name in CERTIFICATES]
    finally:
        if stage != Path(".") and stage.exists():
            shutil.rmtree(stage)


def verify(config: Config, lean: Path, mathlib: Path, output: Path) -> VerificationResult:
    order = preflight(config)
    output_lexical = Path(os.path.abspath(output))
    lean, mathlib, output = Path(lean).resolve(), Path(mathlib).resolve(), output_lexical.resolve()
    lean_mode = lean.lstat().st_mode if lean.exists() else 0
    require(lean.is_file() and not lean.is_symlink() and stat.S_ISREG(lean_mode) and mathlib.is_dir() and not output.exists(),
            "missing build input or nonfresh output")
    install = lean.parent.parent
    require(lean.parent.name == "bin" and install.is_dir() and not install.is_symlink(), "compiler is not in a selected install")
    require(output_lexical == output and not output.parent.is_symlink(), "output path contains an alias")
    require(not output.is_relative_to(config.root) and not output.is_relative_to(install) and not output.is_relative_to(mathlib),
            "output must be isolated from build inputs")
    clean_env = {"PATH": os.defpath, "LANG": "C", "LC_ALL": "C"}
    compiler_evidence = {"sha256": sha256_file(lean), "bytes": lean.stat().st_size}
    version = _run_lean(lean, compiler_evidence, ["--version"], config.root, clean_env)
    require(re.fullmatch(r"Lean \(version 4\.19\.0, [A-Za-z0-9_.-]+, commit 6caaee842e94(?:, (?:Release|Debug))?\)\n?", version) is not None,
            "Lean toolchain validation failed")
    libdir = Path(_run_lean(lean, compiler_evidence, ["--print-libdir"], config.root, clean_env).strip()).resolve()
    expected_libdir = install / "lib" / "lean"
    init_olean = expected_libdir / "Init.olean"
    require(libdir == expected_libdir and libdir.is_dir() and not libdir.is_symlink() and init_olean.is_file() and
            not init_olean.is_symlink() and stat.S_ISREG(init_olean.lstat().st_mode), "Lean standard library evidence missing")
    require(not output.is_relative_to(libdir), "output must be isolated from compiler library")
    git = _helper("git")
    revision = _run([str(git), "-C", str(mathlib), "rev-parse", "HEAD"], config.root, clean_env).strip()
    require(revision == MATHLIB_REVISION, "Mathlib revision validation failed")
    require(_run([str(git), "-C", str(mathlib), "cat-file", "-e", revision + "^{commit}"], config.root, clean_env) == "",
            "Mathlib HEAD is not a commit")
    require(_run([str(git), "-C", str(mathlib), "diff", "--exit-code", "HEAD", "--", "*.lean", "lake-manifest.json"], config.root, clean_env) == "",
            "Mathlib checkout is dirty")
    manifest = mathlib / "lake-manifest.json"
    require(manifest.is_file(), "Mathlib manifest evidence missing")
    manifest_evidence = {"sha256": sha256_file(manifest), "bytes": manifest.stat().st_size}
    cache = mathlib / ".lake" / "build" / "lib" / "lean"
    require(cache.is_dir(), "Mathlib build cache missing")
    dependency_caches, dependency_revisions = _dependency_caches(mathlib, git, config.root, clean_env)
    dependency_paths = tuple(path for _, path in dependency_caches)
    require(not any(output.is_relative_to(root) for root in dependency_paths), "output must be isolated from dependency cache")
    for root in (cache, libdir, *dependency_paths):
        require(not (root / "ArithmeticClock.olean").exists(), "old facade object in compiler search path")
        for module in MODULES:
            require(not (root / Path(local_source_path(module)).with_suffix(".olean")).exists(),
                    "old local object in compiler search path")
    with tempfile.TemporaryDirectory(prefix="arithmetic-clock-run-", dir=output.parent) as temporary:
        run = Path(temporary)
        source, build = run / "source", run / "build"
        source.mkdir(); build.mkdir()
        for item in config.modules:
            target = source / item.source
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(_package_file(config, item.source), target)
            _check_relocated_input(config, target, item.sha256, item.bytes, "relocated source")
        env = dict(clean_env)
        env["LEAN_PATH"] = os.pathsep.join((str(build), str(cache), *(str(item) for item in dependency_paths), str(libdir)))
        object_hashes: dict[str, str] = {}
        dependency_hashes: dict[str, tuple[str, Path]] = {}
        external_roots = (("@mathlib", cache), *dependency_caches, ("@lean/lib", libdir))
        def relocated_integrity() -> None:
            for item in config.modules:
                copied = source / item.source
                _check_relocated_input(config, copied, item.sha256, item.bytes, "relocated source")
        def observe(source_path: Path, expected_sha256: str, expected_bytes: int, label: str) -> None:
            relocated_integrity()
            _check_relocated_input(config, source_path, expected_sha256, expected_bytes, label)
            for logical, value in _check_deps(lean, compiler_evidence, config, source_path,
                    expected_sha256, expected_bytes, label, run, env, build, external_roots).items():
                if logical.startswith("@run/build/"):
                    require(logical in object_hashes and object_hashes[logical] == value[0],
                            "dependency used a current or future local object")
                require(logical not in dependency_hashes or dependency_hashes[logical] == value,
                        "dependency observation changed")
                dependency_hashes[logical] = value
            _check_relocated_input(config, source_path, expected_sha256, expected_bytes, label)
            relocated_integrity()
        for module in order:
            module_config = next(item for item in config.modules if item.name == module)
            relative = Path(local_source_path(module))
            target = build / relative.with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            require(not target.exists(), "fresh object target already exists")
            observe(source / relative, module_config.sha256, module_config.bytes, "relocated source")
            require(not target.exists(), "dependency probe created fresh object target")
            relocated_integrity()
            transcript = _run_fifo_lean(config, lean, compiler_evidence, source / relative,
                module_config.sha256, module_config.bytes, "relocated source",
                ["-DwarningAsError=true", "-o", target.relative_to(run).as_posix()], run, env)
            relocated_integrity()
            require(re.search(REGEX_WORD_BOUNDARY + r"(?:warning|error):", transcript) is None,
                    "production build emitted diagnostics")
            require(target.is_file() and not target.is_symlink(), "compiler did not emit required object")
            _compiled_privacy_scan(config, target, env)
            object_hashes["@run/build/" + relative.with_suffix(".olean").as_posix()] = sha256_file(target)
        audit_source = source / "Audit.lean"
        newline = chr(10)
        audit_source.write_text(newline.join("import " + item for item in config.entries) +
            newline + "set_option pp.all true" + newline + newline.join(
                "#check \"__AUDIT_BEGIN " + item.name + "\"" + newline + "#print " + item.name +
                newline + "#check \"__AUDIT_KIND_END " + item.name + "\"" + newline + "#check @" + item.name +
                newline + "#check \"__AUDIT_TYPE_END " + item.name + "\"" + newline + "#print axioms " + item.name +
                newline + "#check \"__AUDIT_AXIOM_END " + item.name + "\"" + newline +
                "#check \"__AUDIT_END " + item.name + "\"" for item in config.declarations) + newline, encoding="utf-8")
        audit_binding = (sha256_file(audit_source), audit_source.stat().st_size)
        _check_relocated_input(config, audit_source, *audit_binding, "generated audit source")
        observe(audit_source, *audit_binding, "generated audit source")
        _check_relocated_input(config, audit_source, *audit_binding, "generated audit source")
        audit_transcript = _run_bound_lean(config, lean, compiler_evidence, audit_source,
            *audit_binding, "generated audit source", ["-DwarningAsError=true"], run, env)
        _check_relocated_input(config, audit_source, *audit_binding, "generated audit source")
        relocated_integrity()
        require(re.search(REGEX_WORD_BOUNDARY + r"(?:warning|error):", audit_transcript) is None,
                "audit emitted diagnostics")
        audit = parse_audit(config, audit_transcript)
        invalid = source / "InvalidFalse.lean"
        invalid.write_text("import " + config.entries[-1] + newline +
                           "example : False := by exact True.intro" + newline, encoding="utf-8")
        invalid_binding = (sha256_file(invalid), invalid.stat().st_size)
        _check_relocated_input(config, invalid, *invalid_binding, "generated invalid-False source")
        observe(invalid, *invalid_binding, "generated invalid-False source")
        _check_relocated_input(config, invalid, *invalid_binding, "generated invalid-False source")
        code, transcript = _negative_bound_lean(config, lean, compiler_evidence, invalid,
            *invalid_binding, "generated invalid-False source", ["-DwarningAsError=true"], run, env)
        _check_relocated_input(config, invalid, *invalid_binding, "generated invalid-False source")
        relocated_integrity()
        statuses = {"invalid_false": validate_control("invalid_false", code, transcript, ("True.intro", "False"))}
        relocated_controls: list[tuple[Path, str, int]] = []
        for control in config.controls:
            target = source / ("Control_" + control.name + ".lean")
            original_control = _package_file(config, control.source)
            control_binding = (control.sha256, original_control.stat().st_size)
            shutil.copyfile(original_control, target)
            _check_relocated_input(config, target, *control_binding, "relocated control")
            observe(target, *control_binding, "relocated control")
            _check_relocated_input(config, target, *control_binding, "relocated control")
            _check_relocated_input(config, target, *control_binding, "relocated control")
            code, transcript = _negative_bound_lean(config, lean, compiler_evidence, target,
                *control_binding, "relocated control", ["-DwarningAsError=true"], run, env)
            _check_relocated_input(config, target, *control_binding, "relocated control")
            relocated_integrity()
            statuses[control.name] = validate_control(control.name, code, transcript, ("0 = 0", "30 = 0"))
            relocated_controls.append((target, *control_binding))
        expected_objects = _expected_objects()
        require(set(object_hashes) == expected_objects and len(object_hashes) == 9, "fresh object set differs")
        for logical, digest in object_hashes.items():
            relative = logical.removeprefix("@run/build/")
            require(sha256_file(build / relative) == digest, "fresh object changed before publication")
        for logical, (digest, path) in dependency_hashes.items():
            require(sha256_file(path) == digest, "resolved dependency changed before publication")
        relocated_integrity()
        for target, digest, size in relocated_controls:
            _check_relocated_input(config, target, digest, size, "relocated control")
        _check_relocated_input(config, audit_source, *audit_binding, "generated audit source")
        _check_relocated_input(config, invalid, *invalid_binding, "generated invalid-False source")
        require(sha256_file(lean) == compiler_evidence["sha256"] and lean.stat().st_size == compiler_evidence["bytes"], "compiler changed before publication")
        require(sha256_file(manifest) == manifest_evidence["sha256"] and manifest.stat().st_size == manifest_evidence["bytes"], "Mathlib manifest changed before publication")
        for item in config.modules:
            original = _package_file(config, item.source)
            require(sha256_file(original) == item.sha256 and original.stat().st_size == item.bytes,
                    "source changed during verification")
        for control in config.controls:
            require(sha256_file(_package_file(config, control.source)) == control.sha256,
                    "control changed during verification")
        result = VerificationResult(config, order, audit, statuses,
            {"status": "PASS", "lean": "@lean", "mathlib": "@mathlib", "manifest": "@mathlib/lake-manifest.json",
             "objects": object_hashes,
             "direct_dependencies": {logical: digest for logical, (digest, _) in sorted(dependency_hashes.items())},
             "dependency_evidence_scope": "lean-direct-import-objects-only",
             "external_cache_boundary": "pinned-checkouts-with-prebuilt-objects-reused",
             "dependency_revisions": dependency_revisions, "external_caches_reused": True,
             "compiler": compiler_evidence, "mathlib_manifest": manifest_evidence})
        emit_certificates(result, output, build)
        return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package", required=True, type=Path)
    parser.add_argument("--privacy-policy", required=True, type=Path)
    parser.add_argument("--lean", required=True, type=Path)
    parser.add_argument("--mathlib", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    verify(load_config(args.package, args.privacy_policy), args.lean, args.mathlib, args.output)


if __name__ == "__main__":
    main()
