"""Build the deterministic, certified arithmetic-clock release archive."""
from __future__ import annotations

import argparse
import errno
import hashlib
import json
import os
import stat
import sys
import tempfile
import zipfile
from pathlib import Path
from typing import Any

# A direct CLI run must not add bytecode to the exact public package tree.
sys.dont_write_bytecode = True

try:
    from . import verify as verifier
    from .pack_common import BUILD_ORDER, MODULES, add_exception_note, local_source_path, safe_relative
except ImportError:  # Direct CLI execution has no package parent.
    import verify as verifier
    from pack_common import BUILD_ORDER, MODULES, add_exception_note, local_source_path, safe_relative


MANIFEST_NAME = "MANIFEST.json"
CHECKSUM_NAME = "SHA256SUMS"
RELEASE = "arithmetic-clock-proof-pack-v1.0.0"
FIXED_TIMESTAMP = (1980, 1, 1, 0, 0, 0)
STATIC_MEMBER_COUNT = 24
PAYLOAD_MEMBER_COUNT = 41
CHECKSUM_MEMBER_COUNT = 42
ARCHIVE_MEMBER_COUNT = 43
MAX_MEMBER_BYTES = 64 * 1024 * 1024
MAX_ARCHIVE_BYTES = 256 * 1024 * 1024


class PackagingError(RuntimeError):
    """A release gate failed before publication."""


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise PackagingError(message)


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _same_exact(actual: Any, expected: Any) -> bool:
    """Compare certificate data without Python's bool/int/float coercions."""
    if type(actual) is not type(expected):
        return False
    if isinstance(expected, dict):
        return (set(actual) == set(expected) and
                all(_same_exact(actual[key], value) for key, value in expected.items()))
    if isinstance(expected, list):
        return len(actual) == len(expected) and all(
            _same_exact(left, right) for left, right in zip(actual, expected)
        )
    return actual == expected


def _read_regular(path: Path, message: str) -> bytes:
    try:
        mode = path.lstat().st_mode
    except OSError as exc:
        raise PackagingError(message) from exc
    _require(not path.is_symlink() and stat.S_ISREG(mode), message)
    try:
        raw = path.read_bytes()
    except OSError as exc:
        raise PackagingError(message) from exc
    _require(len(raw) <= MAX_MEMBER_BYTES, "release member exceeds size limit")
    return raw


def _strict_json(raw: bytes) -> dict[str, Any]:
    def no_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise PackagingError("duplicate certificate key")
            result[key] = value
        return result

    try:
        value = json.loads(
            raw.decode("ascii"),
            object_pairs_hook=no_duplicates,
            parse_constant=lambda _: (_ for _ in ()).throw(PackagingError("invalid certificate number")),
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise PackagingError("invalid certificate JSON") from exc
    _require(isinstance(value, dict), "certificate must be an object")
    return value


def _expected_paths(config: verifier.Config) -> tuple[set[str], set[str], set[str]]:
    static = {"package.json"} | {path for path, _, _ in config.public_files}
    _require(len(static) == STATIC_MEMBER_COUNT, "static release allowlist differs")
    objects = {
        "verification/build/" + Path(local_source_path(module)).with_suffix(".olean").as_posix()
        for module in MODULES
    }
    certificates = {
        "verification/certificates/" + name for name in verifier.CERTIFICATES
    }
    payload = static | objects | certificates | {"verification/types-and-axioms.txt"}
    _require(len(objects) == len(MODULES) == 9 and len(certificates) == 7 and
             len(payload) == PAYLOAD_MEMBER_COUNT, "final release allowlist differs")
    return static, objects, payload


def _scan_tree(project: Path, expected_payload: set[str]) -> tuple[set[str], bool]:
    files: set[str] = set()
    directories: set[str] = set()
    folded: set[str] = set()
    for path in project.rglob("*"):
        relative = path.relative_to(project).as_posix()
        try:
            mode = path.lstat().st_mode
        except OSError as exc:
            raise PackagingError("release tree changed during inspection") from exc
        _require(not path.is_symlink(), "release tree contains an alias")
        _require(path.is_dir() or stat.S_ISREG(mode), "release tree contains a special member")
        _require(relative.casefold() not in folded, "release tree has a case-fold collision")
        folded.add(relative.casefold())
        if path.is_dir():
            directories.add(relative)
        else:
            try:
                safe_relative(relative)
            except ValueError as exc:
                raise PackagingError("release tree contains an invalid member name") from exc
            files.add(relative)
    metadata = {MANIFEST_NAME, CHECKSUM_NAME}
    metadata_present = files & metadata
    _require(not metadata_present or metadata_present == metadata,
             "release metadata must be absent or a complete pair")
    expected_files = expected_payload | metadata_present
    _require(files == expected_files, "release tree differs from exact allowlist")
    expected_directories = verifier._ancestor_directories(expected_payload | metadata)
    _require(directories == expected_directories, "release directory topology differs")
    return files, bool(metadata_present)


def _snapshot_static(config: verifier.Config, static: set[str]) -> tuple[dict[str, bytes], list[dict[str, Any]]]:
    table = {path: (digest, size) for path, digest, size in config.public_files}
    _require(len(table) == len(config.public_files), "duplicate static member binding")
    raw_by_path: dict[str, bytes] = {}
    rows: list[dict[str, Any]] = []
    for relative in sorted(static):
        raw = _read_regular(config.root / relative, "static member is missing or invalid")
        digest = _sha256(raw)
        if relative == "package.json":
            _require(digest == config.package_sha256, "package configuration binding differs")
        else:
            expected = table.get(relative)
            _require(expected == (digest, len(raw)), "static member hash or size differs")
        try:
            verifier._privacy_scan(config, config.root / relative, raw)
        except verifier.VerificationError as exc:
            raise PackagingError("static privacy gate failed") from exc
        raw_by_path[relative] = raw
        rows.append({"path": "@package/" + relative, "sha256": digest, "bytes": len(raw)})
    _require(len(rows) == STATIC_MEMBER_COUNT, "static member count differs")
    return raw_by_path, rows


def _common_certificate(config: verifier.Config) -> dict[str, Any]:
    return {
        "schema_version": 1,
        "status": "PASS",
        "scope": "arithmetic-clock",
        "inputs": [
            {"path": "@package/" + item.source, "sha256": item.sha256, "bytes": item.bytes}
            for item in config.modules
        ],
        "hashes": {
            "package_config": config.package_sha256,
            "facade": config.facade_sha256,
            "wrong_period": verifier.CONTROL_SHA256,
        },
        "toolchain": {
            "lean_version": verifier.LEAN_VERSION,
            "lean_commit": verifier.LEAN_COMMIT,
            "mathlib_revision": verifier.MATHLIB_REVISION,
        },
    }


def _require_keys(document: dict[str, Any], expected: set[str], label: str) -> None:
    _require(set(document) == expected, label + " certificate schema differs")


def _validate_certificates(
    config: verifier.Config,
    raw_by_path: dict[str, bytes],
    public_members: list[dict[str, Any]],
) -> tuple[dict[str, dict[str, Any]], dict[str, str], dict[str, Any]]:
    documents: dict[str, dict[str, Any]] = {}
    for name in verifier.CERTIFICATES:
        relative = "verification/certificates/" + name
        raw = raw_by_path[relative]
        document = _strict_json(raw)
        _require(raw == verifier._canonical(document), "certificate is not canonical")
        _require(type(document.get("schema_version")) is int and document.get("schema_version") == 1 and
                 document.get("status") == "PASS" and document.get("scope") == "arithmetic-clock",
                 "certificate status or identity differs")
        try:
            verifier._validate_certificate_paths(document)
        except verifier.VerificationError as exc:
            raise PackagingError("certificate path gate failed") from exc
        documents[name] = document

    common = _common_certificate(config)
    for name in verifier.CERTIFICATES:
        if name == "PRIVACY_CERTIFICATE.json":
            continue
        document = documents[name]
        for key, expected in common.items():
            _require(key in document and _same_exact(document[key], expected),
                     "certificate input binding differs")

    source = documents["SOURCE_CERTIFICATE.json"]
    _require_keys(source, set(common) | {"source_count", "facade", "public_members",
                                        "public_member_count", "public_member_table_sha256"}, "source")
    public_table_hash = _sha256(verifier._canonical(public_members))
    _require(type(source["source_count"]) is int and source["source_count"] == 9 and
             source["facade"] == "@package/ArithmeticClock.lean" and
             _same_exact(source["public_members"], public_members) and
             type(source["public_member_count"]) is int and
             source["public_member_count"] == STATIC_MEMBER_COUNT and
             source["public_member_table_sha256"] == public_table_hash,
             "source certificate member binding differs")

    build = documents["BUILD_CERTIFICATE.json"]
    build_fields = {
        "module_order", "fresh", "paths", "objects", "direct_dependencies",
        "dependency_revisions", "dependency_evidence_scope", "external_cache_boundary",
        "external_caches_reused", "compiler", "mathlib_manifest", "type_axiom_artifact",
    }
    _require_keys(build, set(common) | build_fields, "build")
    _require(_same_exact(build["module_order"], list(BUILD_ORDER)) and build["fresh"] is True and
             _same_exact(build["paths"], {"lean": "@lean", "mathlib": "@mathlib",
                                           "manifest": "@mathlib/lake-manifest.json"}),
             "build certificate selection differs")
    evidence_fields = {
        "status", "lean", "mathlib", "manifest", "objects", "direct_dependencies",
        "dependency_revisions", "dependency_evidence_scope", "external_cache_boundary",
        "external_caches_reused", "compiler", "mathlib_manifest",
    }
    evidence = {
        "status": build["status"],
        "lean": build["paths"]["lean"],
        "mathlib": build["paths"]["mathlib"],
        "manifest": build["paths"]["manifest"],
        **{key: build[key] for key in evidence_fields - {"status", "lean", "mathlib", "manifest"}},
    }
    try:
        verifier._validate_build_evidence(evidence)
    except verifier.VerificationError as exc:
        raise PackagingError("build certificate evidence differs") from exc

    declaration = documents["DECLARATION_CERTIFICATE.json"]
    axiom = documents["AXIOM_CERTIFICATE.json"]
    _require_keys(declaration, set(common) | {"declaration_count", "literal_types",
                                             "type_axiom_artifact"}, "declaration")
    _require_keys(axiom, set(common) | {"allowed_axioms", "transitive_axioms",
                                       "type_axiom_artifact"}, "axiom")
    _require(type(declaration["declaration_count"]) is int and
             declaration["declaration_count"] == 203 and
             isinstance(declaration["literal_types"], dict) and
             isinstance(axiom["transitive_axioms"], dict) and
             axiom["allowed_axioms"] == sorted(verifier.ALLOWED_AXIOMS),
             "declaration or axiom certificate summary differs")
    declaration_names = {item.name for item in config.declarations}
    _require(set(declaration["literal_types"]) == declaration_names and
             set(axiom["transitive_axioms"]) == declaration_names,
             "declaration or axiom certificate selection differs")
    audit = {
        name: (literal, axiom["transitive_axioms"].get(name))
        for name, literal in declaration["literal_types"].items()
    }
    _require(all(isinstance(literal, str) and literal for literal in declaration["literal_types"].values()) and
             all(isinstance(value, list) and all(isinstance(item, str) for item in value)
                 for value in axiom["transitive_axioms"].values()) and
             all(value == sorted(set(value))
                 for value in axiom["transitive_axioms"].values()),
             "declaration or axiom certificate payload differs")
    try:
        verifier.validate_audit(config, audit)
    except verifier.VerificationError as exc:
        raise PackagingError("declaration or axiom certificate binding differs") from exc

    control = documents["CONTROL_CERTIFICATE.json"]
    _require_keys(control, set(common) | {"controls"}, "control")
    expected_controls = {
        name: {"status": "PASS", "diagnostic_class": "lean-4.19-type-mismatch",
               "normalized_sha256": digest}
        for name, digest in verifier.CONTROL_DIGESTS.items()
    }
    _require(control["controls"] == expected_controls, "control certificate binding differs")

    privacy = documents["PRIVACY_CERTIFICATE.json"]
    privacy_fields = {
        "schema_version", "status", "scope", "inputs", "hashes", "finding_count",
        "member_count", "member_table_sha256", "retained_members", "retained_member_count",
    }
    _require_keys(privacy, privacy_fields, "privacy")
    _require(_same_exact(privacy["inputs"], public_members) and
             _same_exact(privacy["hashes"], {"external_policy": config.policy_sha256}) and
             type(privacy["finding_count"]) is int and privacy["finding_count"] == 0 and
             type(privacy["member_count"]) is int and privacy["member_count"] == STATIC_MEMBER_COUNT and
             privacy["member_table_sha256"] == public_table_hash and
             type(privacy["retained_member_count"]) is int and
             privacy["retained_member_count"] == len(MODULES) + 1,
             "privacy certificate binding differs")

    artifact = build["type_axiom_artifact"]
    _require(isinstance(artifact, dict) and set(artifact) == {"path", "sha256", "bytes"} and
             artifact.get("path") == "@run/types-and-axioms.txt" and
             verifier._sha(artifact.get("sha256")) and type(artifact.get("bytes")) is int and
             artifact["bytes"] >= 0 and _same_exact(declaration["type_axiom_artifact"], artifact) and
             _same_exact(axiom["type_axiom_artifact"], artifact),
             "type and axiom artifact binding differs")
    expected_retained = [
        *[{"path": path, "sha256": digest} for path, digest in sorted(build["objects"].items())],
        artifact,
    ]
    _require(_same_exact(privacy["retained_members"], expected_retained),
             "privacy retained artifact binding differs")

    reproducibility = documents["REPRODUCIBILITY_CERTIFICATE.json"]
    _require_keys(reproducibility, set(common) | {"canonical_json", "source_hashes",
                                                  "certificate_hashes"}, "reproducibility")
    expected_certificate_hashes = {
        name: _sha256(raw_by_path["verification/certificates/" + name])
        for name in verifier.CERTIFICATES[:-1]
    }
    _require(reproducibility["canonical_json"] is True and
             reproducibility["source_hashes"] == {item.source: item.sha256 for item in config.modules} and
             reproducibility["certificate_hashes"] == expected_certificate_hashes,
             "reproducibility certificate graph differs")

    objects = build["objects"]
    _require(isinstance(objects, dict), "compiled artifact binding differs")
    return documents, objects, artifact


def _validate_artifacts(
    config: verifier.Config,
    raw_by_path: dict[str, bytes],
    documents: dict[str, dict[str, Any]],
    objects: dict[str, str],
    artifact: dict[str, Any],
) -> None:
    try:
        verifier._validate_final_stage(config.root / "verification", config, objects, artifact, documents)
    except verifier.VerificationError as exc:
        raise PackagingError("compiled or certificate artifact binding differs") from exc

    for logical in sorted(objects):
        relative = logical.removeprefix("@run/build/")
        release_path = "verification/build/" + relative
        _require(release_path in raw_by_path and _sha256(raw_by_path[release_path]) == objects[logical],
                 "compiled artifact binding differs")
        try:
            verifier._compiled_privacy_scan(config, config.root / release_path,
                                            {"PATH": os.defpath, "LANG": "C", "LC_ALL": "C"})
        except verifier.VerificationError as exc:
            raise PackagingError("compiled privacy gate failed") from exc

    for relative, raw in raw_by_path.items():
        if relative.endswith(".olean"):
            continue
        try:
            verifier._privacy_scan(config, config.root / relative, raw)
        except verifier.VerificationError as exc:
            raise PackagingError("final privacy gate failed") from exc


def _manifest_bytes(payload: dict[str, bytes]) -> bytes:
    rows = [
        {"path": path, "sha256": _sha256(raw), "bytes": len(raw)}
        for path, raw in sorted(payload.items())
    ]
    _require(len(rows) == PAYLOAD_MEMBER_COUNT, "manifest payload count differs")
    document = {
        "schema_version": 1,
        "project": "arithmetic-clock",
        "release": RELEASE,
        "archive_member_count": ARCHIVE_MEMBER_COUNT,
        "payload_member_count": PAYLOAD_MEMBER_COUNT,
        "manifest_scope": "payload-members-only",
        "checksum_scope": "all-members-except-SHA256SUMS",
        "members": rows,
    }
    return verifier._canonical(document)


def _checksum_bytes(payload: dict[str, bytes], manifest: bytes) -> bytes:
    covered = {**payload, MANIFEST_NAME: manifest}
    _require(len(covered) == CHECKSUM_MEMBER_COUNT, "checksum member count differs")
    return "".join(_sha256(raw) + "  " + path + "\n" for path, raw in sorted(covered.items())).encode("ascii")


def _validate_release_metadata(payload: dict[str, bytes], manifest: bytes, checksums: bytes) -> None:
    document = _strict_json(manifest)
    _require(manifest == verifier._canonical(document), "manifest is not canonical")
    _require(set(document) == {"schema_version", "project", "release", "archive_member_count",
                               "payload_member_count", "manifest_scope", "checksum_scope", "members"} and
             type(document.get("schema_version")) is int and document["schema_version"] == 1 and
             document.get("project") == "arithmetic-clock" and document.get("release") == RELEASE and
             document.get("archive_member_count") == ARCHIVE_MEMBER_COUNT and
             document.get("payload_member_count") == PAYLOAD_MEMBER_COUNT and
             document.get("manifest_scope") == "payload-members-only" and
             document.get("checksum_scope") == "all-members-except-SHA256SUMS",
             "manifest schema differs")
    expected_rows = [
        {"path": path, "sha256": _sha256(raw), "bytes": len(raw)}
        for path, raw in sorted(payload.items())
    ]
    _require(document.get("members") == expected_rows, "manifest member binding differs")
    try:
        lines = checksums.decode("ascii").splitlines(keepends=True)
    except UnicodeDecodeError as exc:
        raise PackagingError("checksum file is not ASCII") from exc
    _require(len(lines) == CHECKSUM_MEMBER_COUNT and all(line.endswith("\n") for line in lines),
             "checksum row count or framing differs")
    expected_covered = {**payload, MANIFEST_NAME: manifest}
    seen: set[str] = set()
    for line, (expected_path, expected_raw) in zip(lines, sorted(expected_covered.items())):
        body = line[:-1]
        digest, separator, path = body.partition("  ")
        _require(separator == "  " and path == expected_path and path not in seen and
                 digest == _sha256(expected_raw), "checksum binding differs")
        seen.add(path)
    _require(CHECKSUM_NAME not in seen and seen == set(expected_covered), "checksum scope differs")


def _zip_info(path: str) -> zipfile.ZipInfo:
    info = zipfile.ZipInfo(path, FIXED_TIMESTAMP)
    info.compress_type = zipfile.ZIP_STORED
    info.create_system = 3
    info.external_attr = (stat.S_IFREG | 0o644) << 16
    info.internal_attr = 0
    info.extra = b""
    info.comment = b""
    return info


def _write_zip(path: Path, members: dict[str, bytes]) -> None:
    with zipfile.ZipFile(path, "w", compression=zipfile.ZIP_STORED, allowZip64=False) as archive:
        archive.comment = b""
        for name, raw in sorted(members.items()):
            archive.writestr(_zip_info(name), raw)
    with path.open("rb") as stream:
        os.fsync(stream.fileno())


def _validate_zip(path: Path, members: dict[str, bytes], config: verifier.Config) -> None:
    _require(path.stat().st_size <= MAX_ARCHIVE_BYTES, "archive exceeds size limit")
    try:
        with zipfile.ZipFile(path, "r", allowZip64=False) as archive:
            infos = archive.infolist()
            names = [info.filename for info in infos]
            _require(len(infos) == ARCHIVE_MEMBER_COUNT and names == sorted(members) and
                     len({name.casefold() for name in names}) == ARCHIVE_MEMBER_COUNT,
                     "archive member allowlist differs")
            _require(archive.comment == b"" and archive.testzip() is None, "archive integrity differs")
            for info in infos:
                try:
                    safe_relative(info.filename)
                except ValueError as exc:
                    raise PackagingError("archive contains an invalid member name") from exc
                _require(info.date_time == FIXED_TIMESTAMP and info.compress_type == zipfile.ZIP_STORED and
                         info.create_system == 3 and stat.S_IFMT(info.external_attr >> 16) == stat.S_IFREG and
                         stat.S_IMODE(info.external_attr >> 16) == 0o644 and not info.extra and not info.comment and
                         not (info.flag_bits & 1) and not info.is_dir(),
                         "archive member metadata differs")
                raw = archive.read(info)
                _require(raw == members[info.filename] and info.file_size == len(raw),
                         "archive member bytes differ")
    except (OSError, zipfile.BadZipFile, NotImplementedError, RuntimeError) as exc:
        if isinstance(exc, PackagingError):
            raise
        raise PackagingError("archive validation failed") from exc
    try:
        archive_raw = path.read_bytes()
    except OSError as exc:
        raise PackagingError("temporary archive is invalid") from exc
    _require(not any(token.encode("utf-8") in archive_raw for token in config.policy_tokens),
             "archive privacy gate failed")


def _identity(value: os.stat_result) -> tuple[int, int]:
    return value.st_dev, value.st_ino


def _unlink_owned(path: Path, identity: tuple[int, int], *, mismatch_ok: bool = False) -> None:
    """Unlink only the filesystem object whose identity we recorded."""
    try:
        current = path.lstat()
    except FileNotFoundError:
        return
    except OSError as exc:
        raise PackagingError("could not inspect an owned release file") from exc
    if _identity(current) != identity:
        _require(mismatch_ok, "an owned release file was replaced")
        return
    try:
        path.unlink()
    except FileNotFoundError:
        pass


def _record_cleanup(
    primary: BaseException | None, cleanup: BaseException, label: str
) -> BaseException:
    if primary is None:
        return cleanup
    add_exception_note(primary, label + ": " + str(cleanup))
    return primary


def _exclusive_write(
    path: Path,
    raw: bytes,
    ownership: dict[Path, tuple[int, int]] | None = None,
) -> None:
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = -1
    identity: tuple[int, int] | None = None
    owned = ownership if ownership is not None else {}
    primary: BaseException | None = None
    try:
        descriptor = os.open(path, flags, 0o644)
        opened = os.fstat(descriptor)
        _require(stat.S_ISREG(opened.st_mode), "release metadata target is not regular")
        identity = _identity(opened)
        _require(path not in owned, "release metadata ownership is duplicated")
        owned[path] = identity
        offset = 0
        while offset < len(raw):
            try:
                written = os.write(descriptor, raw[offset:])
            except InterruptedError:
                continue
            if type(written) is not int or written <= 0:
                raise OSError(errno.EIO, "release metadata write stalled")
            offset += written
        os.fsync(descriptor)
    except BaseException as exc:
        primary = exc
        if identity is None and descriptor >= 0:
            try:
                opened = os.fstat(descriptor)
                if stat.S_ISREG(opened.st_mode):
                    identity = _identity(opened)
                    owned[path] = identity
            except BaseException as cleanup:
                primary = _record_cleanup(
                    primary, cleanup, "release metadata ownership recovery failed"
                )
    if descriptor >= 0:
        try:
            os.close(descriptor)
        except BaseException as cleanup:
            primary = _record_cleanup(
                primary, cleanup, "release metadata descriptor cleanup failed"
            )
    if primary is not None:
        if identity is not None:
            try:
                _unlink_owned(path, identity)
            except BaseException as cleanup:
                primary = _record_cleanup(
                    primary, cleanup, "partial release metadata cleanup failed"
                )
        if isinstance(primary, OSError):
            raise PackagingError("could not install release metadata") from primary
        raise primary


def _stable_snapshot(project: Path, snapshot: dict[str, bytes]) -> None:
    for relative, expected in snapshot.items():
        _require(_read_regular(project / relative, "release input changed before publication") == expected,
                 "release input changed before publication")


def package_release(project: Path, output: Path, privacy_policy: Path) -> Path:
    """Validate a complete PASS tree and publish one exact deterministic ZIP."""
    project_input = Path(project)
    try:
        project_mode = project_input.lstat().st_mode
    except OSError as exc:
        raise PackagingError("project root is missing") from exc
    _require(project_input.is_dir() and not project_input.is_symlink() and stat.S_ISDIR(project_mode),
             "project root is invalid")
    project = project_input.resolve()
    _require(Path(os.path.abspath(project_input)) == project, "project root contains an alias")

    output_lexical = Path(os.path.abspath(output))
    output_resolved = output_lexical.resolve(strict=False)
    _require(output_lexical.suffix == ".zip", "output must be a ZIP path")
    _require(not output_lexical.exists() and not output_lexical.is_symlink(), "output must be fresh")
    _require(not output_lexical.is_relative_to(project) and not output_resolved.is_relative_to(project),
             "output must be outside the project")

    policy_input = Path(privacy_policy)
    try:
        policy_mode = policy_input.lstat().st_mode
    except OSError as exc:
        raise PackagingError("external privacy policy is missing") from exc
    _require(policy_input.is_file() and not policy_input.is_symlink() and stat.S_ISREG(policy_mode),
             "external privacy policy is invalid")
    policy = policy_input.resolve()
    try:
        config = verifier.load_config(project / "package.json", policy)
    except verifier.VerificationError as exc:
        raise PackagingError("public package configuration failed validation") from exc

    static, _, payload_paths = _expected_paths(config)
    _, metadata_present = _scan_tree(project, payload_paths)
    static_raw, public_members = _snapshot_static(config, static)
    _require(verifier.sha256_file(policy) == config.policy_sha256,
             "external privacy policy changed during validation")

    raw_by_path = dict(static_raw)
    for relative in sorted(payload_paths - static):
        raw_by_path[relative] = _read_regular(project / relative, "verification artifact is missing or invalid")
    _require(len(raw_by_path) == PAYLOAD_MEMBER_COUNT and
             sum(len(raw) for raw in raw_by_path.values()) <= MAX_ARCHIVE_BYTES,
             "release payload size or count differs")
    documents, objects, artifact = _validate_certificates(config, raw_by_path, public_members)
    _validate_artifacts(config, raw_by_path, documents, objects, artifact)

    manifest = _manifest_bytes(raw_by_path)
    checksums = _checksum_bytes(raw_by_path, manifest)
    _validate_release_metadata(raw_by_path, manifest, checksums)
    try:
        verifier._privacy_scan(config, project / MANIFEST_NAME, manifest)
        verifier._privacy_scan(config, project / CHECKSUM_NAME, checksums)
    except verifier.VerificationError as exc:
        raise PackagingError("release metadata privacy gate failed") from exc

    if metadata_present:
        _require(_read_regular(project / MANIFEST_NAME, "release metadata is invalid") == manifest and
                 _read_regular(project / CHECKSUM_NAME, "release metadata is invalid") == checksums,
                 "release metadata does not match the current payload")

    _stable_snapshot(project, raw_by_path)
    _require(verifier.sha256_file(policy) == config.policy_sha256,
             "external privacy policy changed before publication")
    _scan_tree(project, payload_paths)

    output_parent = output_lexical.parent
    if not output_parent.exists():
        ancestor = output_parent.parent
        _require(ancestor.is_dir() and not ancestor.is_symlink(), "output parent is invalid")
        try:
            output_parent.mkdir(mode=0o755)
        except OSError as exc:
            raise PackagingError("could not create output parent") from exc
    _require(output_parent.is_dir() and not output_parent.is_symlink(), "output parent is invalid")
    _require(output_parent.resolve() == output_parent and not output_lexical.exists(), "output path contains an alias")

    final_members = {**raw_by_path, MANIFEST_NAME: manifest, CHECKSUM_NAME: checksums}
    _require(len(final_members) == ARCHIVE_MEMBER_COUNT, "archive member count differs")
    temporary: Path | None = None
    temporary_descriptor = -1
    temporary_identity: tuple[int, int] | None = None
    metadata_ownership: dict[Path, tuple[int, int]] = {}
    output_owned = False
    output_link_uncertain = False
    primary: BaseException | None = None
    try:
        temporary_descriptor, temporary_name = tempfile.mkstemp(
            prefix=".arithmetic-clock-release-", suffix=".tmp", dir=output_parent
        )
        temporary = Path(temporary_name)
        temporary_stat = os.fstat(temporary_descriptor)
        _require(stat.S_ISREG(temporary_stat.st_mode), "temporary archive is not regular")
        temporary_identity = _identity(temporary_stat)
        os.close(temporary_descriptor)
        temporary_descriptor = -1
        _write_zip(temporary, final_members)
        os.chmod(temporary, 0o644)
        _validate_zip(temporary, final_members, config)
        _stable_snapshot(project, raw_by_path)
        _require(verifier.sha256_file(policy) == config.policy_sha256,
                 "external privacy policy changed before publication")
        _scan_tree(project, payload_paths)
        if not metadata_present:
            for name, raw in ((MANIFEST_NAME, manifest), (CHECKSUM_NAME, checksums)):
                target = project / name
                _exclusive_write(target, raw, metadata_ownership)
        else:
            _require(_read_regular(project / MANIFEST_NAME, "release metadata is invalid") == manifest and
                     _read_regular(project / CHECKSUM_NAME, "release metadata is invalid") == checksums,
                     "release metadata changed before publication")
        _require(_read_regular(project / MANIFEST_NAME, "release metadata is invalid") == manifest and
                 _read_regular(project / CHECKSUM_NAME, "release metadata is invalid") == checksums,
                 "release metadata changed before publication")
        _stable_snapshot(project, raw_by_path)
        _require(verifier.sha256_file(policy) == config.policy_sha256,
                 "external privacy policy changed before publication")
        _scan_tree(project, payload_paths)
        try:
            os.link(temporary, output_lexical)
        except OSError as exc:
            if exc.errno == errno.EEXIST:
                raise PackagingError("output must be fresh") from exc
            raise PackagingError("could not publish release archive") from exc
        except BaseException:
            output_link_uncertain = True
            raise
        output_owned = True
        installed = output_lexical.lstat()
        _require(temporary_identity is not None and
                 _identity(installed) == temporary_identity and stat.S_ISREG(installed.st_mode),
                 "published archive identity differs")
    except BaseException as exc:
        primary = exc

    if temporary_identity is None and temporary_descriptor >= 0:
        try:
            temporary_stat = os.fstat(temporary_descriptor)
            if stat.S_ISREG(temporary_stat.st_mode):
                temporary_identity = _identity(temporary_stat)
        except BaseException as cleanup:
            primary = _record_cleanup(
                primary, cleanup, "temporary archive ownership recovery failed"
            )
    if temporary_descriptor >= 0:
        try:
            os.close(temporary_descriptor)
        except BaseException as cleanup:
            primary = _record_cleanup(
                primary, cleanup, "temporary archive descriptor cleanup failed"
            )
    if temporary is not None and temporary_identity is not None:
        try:
            _unlink_owned(temporary, temporary_identity)
        except BaseException as cleanup:
            primary = _record_cleanup(primary, cleanup, "temporary archive cleanup failed")
    elif temporary is not None:
        primary = _record_cleanup(
            primary,
            PackagingError("temporary archive ownership is unavailable"),
            "temporary archive cleanup failed",
        )

    if primary is not None:
        if (output_owned or output_link_uncertain) and temporary_identity is not None:
            try:
                _unlink_owned(output_lexical, temporary_identity, mismatch_ok=True)
            except BaseException as cleanup:
                primary = _record_cleanup(primary, cleanup, "published archive rollback failed")
        for target, identity in reversed(tuple(metadata_ownership.items())):
            try:
                _unlink_owned(target, identity)
            except BaseException as cleanup:
                primary = _record_cleanup(primary, cleanup, "release metadata rollback failed")
        if isinstance(primary, OSError):
            raise PackagingError("release publication failed") from primary
        raise primary
    return output_lexical


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build the certified arithmetic-clock release ZIP.")
    parser.add_argument("--project", required=True, type=Path)
    parser.add_argument("--privacy-policy", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        result = package_release(args.project, args.output, args.privacy_policy)
    except PackagingError as exc:
        parser.exit(1, "error: " + str(exc) + "\n")
    print("created " + result.name)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
