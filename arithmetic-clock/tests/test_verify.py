import contextlib
import errno
import hashlib
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
import importlib
import zipfile
from unittest import mock
from pathlib import Path


TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))


NAMES = (
    "ArithmeticClock.CyclicCharacters",
    "ArithmeticClock.DenseCarrier",
    "ArithmeticClock.CyclicTwirl",
    "ArithmeticClock.DenseTwirl",
    "ArithmeticClock.DivisorGram",
    "ArithmeticClock.RealClock60",
    "ArithmeticClock.DivisorGram60",
    "ArithmeticClock.ContinuousReturn60",
    "ArithmeticClock.IntegerClock60",
)
STATIC_PUBLIC = ("README.md", "LICENSE", "__init__.py", "tools/__init__.py", "tools/pack_common.py",
                 "tools/verify.py", "tools/package_release.py", "tests/test_verify.py", "lean-toolchain", "lakefile.toml",
                 "DEPENDENCIES.json", "CLAIM_MAP.json")
EXPLICIT_ARGUMENT_LITERAL = ("@Function.Injective.{1, 1}\n"
                             "  (Fin 12)\n"
                             "  (ZMod (@OfNat.ofNat Nat 60 (instOfNatNat 60)))\n"
                             "  ArithmeticClock.CyclicTwirl.weights60")
UNICODE_EXPLICIT_ARGUMENT_LITERAL = (EXPLICIT_ARGUMENT_LITERAL +
                                     "\n  (∀ z : ℂ, z → z)")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rebind_public(config, relative, path):
    object.__setattr__(config, "public_files", tuple(
        (name, digest(path), path.stat().st_size) if name == relative else (name, value, size)
        for name, value, size in config.public_files))


def policy_file(root):
    policy = root / "external-policy.txt"
    blocked = ["__policy_probe__"]
    policy.write_text(json.dumps({"schema_version": 1, "blocked": blocked}), encoding="utf-8")
    return policy


def static_public_files(package):
    for relative in STATIC_PUBLIC:
        path = package / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        if relative == "lean-toolchain":
            path.write_text("leanprover/lean4:v4.19.0\n", encoding="utf-8")
        elif relative == "lakefile.toml":
            path.write_text(chr(10).join(("name = \"arithmetic-clock\"", "", "[[lean_lib]]",
                "name = \"ArithmeticClock\"", "", "[[require]]", "name = \"mathlib\"",
                "git = \"https://github.com/leanprover-community/mathlib4.git\"",
                "rev = \"c44e0c8ee63ca166450922a373c7409c5d26b00b\"", "")), encoding="utf-8")
        elif relative == "DEPENDENCIES.json":
            path.write_text(json.dumps({"schema_version": 1, "dependencies": __import__("verify").DEPENDENCY_PINS}), encoding="utf-8")
        else:
            path.write_text("fixture " + relative + "\n", encoding="utf-8")


def claim_map(package, declarations):
    endpoints = [row["name"] for row in declarations[:73]]
    counts = [6] * 11 + [7]
    offset = 0
    claims = []
    for number, count in enumerate(counts):
        claims.append({"id": "claim_" + str(number), "kind": "fixture", "endpoints": endpoints[offset:offset + count]})
        offset += count
    claims[-1]["endpoints"].extend(endpoints[:3])
    (package / "CLAIM_MAP.json").write_text(json.dumps({"schema_version": 1, "claims": claims}), encoding="utf-8")


def fixture_pack(root, change=None):
    package = root / "pack"
    source = package / "ArithmeticClock"
    source.mkdir(parents=True)
    rows = []
    declarations = []
    imports_by_module = {
        NAMES[0]: ["Mathlib.Tactic"], NAMES[1]: ["Mathlib.Tactic"], NAMES[2]: [NAMES[0]],
        NAMES[3]: [NAMES[1], NAMES[2]], NAMES[4]: [NAMES[1]], NAMES[5]: [NAMES[3]],
        NAMES[6]: [NAMES[4], NAMES[5]], NAMES[7]: [NAMES[5]], NAMES[8]: [NAMES[7]],
    }
    for index, module in enumerate(NAMES):
        leaf = module.rsplit(".", 1)[1]
        imports = imports_by_module[module]
        owner = "ArithmeticClock.RealClock60" if module in NAMES[-2:] else module
        text = chr(10).join("import " + item for item in imports) + chr(10) + "namespace " + owner + chr(10)
        amount = 6 if index == 0 else (25 if index <= 5 else 24)
        for number in range(amount):
            name = leaf.lower() + "_" + str(number)
            text += "theorem " + name + " : True := True.intro\n"
            declarations.append({"name": owner + "." + name, "module": module,
                                 "kind": "theorem"})
        text += "end " + owner + "\n"
        target = source / (leaf + ".lean")
        target.write_text(text, encoding="utf-8")
        rows.append({"module": module, "source": "ArithmeticClock/" + leaf + ".lean",
                     "sha256": digest(target), "bytes": target.stat().st_size, "imports": imports})
    facade = package / "ArithmeticClock.lean"
    facade.write_text("\n".join("import " + item for item in NAMES[-3:]) + "\n", encoding="utf-8")
    control = package / "controls" / "WrongPeriod.lean"
    control.parent.mkdir()
    control.write_text((Path(__file__).resolve().parents[1] / "controls" / "WrongPeriod.lean").read_text(), encoding="utf-8")
    static_public_files(package)
    claim_map(package, declarations)
    policy = policy_file(root)
    config = {"schema_version": 1, "project": "arithmetic-clock", "toolchain": {
        "lean_version": "4.19.0", "lean_commit": "6caaee842e94",
        "mathlib_revision": "c44e0c8ee63ca166450922a373c7409c5d26b00b"},
        "modules": rows, "entries": list(NAMES[-3:]), "declarations": declarations,
        "kind_totals": {"theorem": 161, "def": 41, "abbrev": 1},
        "allowed_axioms": ["Classical.choice", "Quot.sound", "propext"],
        "negative_controls": [{"name": "wrong_period", "source": "controls/WrongPeriod.lean",
                               "sha256": digest(control)}],
        "facade": {"source": "ArithmeticClock.lean", "sha256": digest(facade), "bytes": facade.stat().st_size,
                   "imports": list(NAMES[-3:])}}
    bound = [(row["source"], row["sha256"], row["bytes"]) for row in rows]
    bound.extend((("ArithmeticClock.lean", digest(facade), facade.stat().st_size),
                  ("controls/WrongPeriod.lean", digest(control), control.stat().st_size)))
    bound.extend((relative, digest(package / relative), (package / relative).stat().st_size) for relative in STATIC_PUBLIC)
    config["public_files"] = [{"path": path, "sha256": value, "bytes": size}
                              for path, value, size in sorted(bound)]
    if change:
        change(package, config, policy)
    manifest = package / "package.json"
    manifest.write_text(json.dumps(config), encoding="utf-8")
    return package, manifest, policy


class VerifierTests(unittest.TestCase):
    def test_tools_are_importable_as_package_modules(self):
        module = importlib.import_module("project.tools.verify")
        self.assertTrue(callable(module.verify))

    def test_direct_cli_help_leaves_the_package_bytecode_free(self):
        with tempfile.TemporaryDirectory() as raw:
            source = Path(__file__).resolve().parents[1]
            package = Path(raw) / "project"
            shutil.copytree(
                source,
                package,
                ignore=shutil.ignore_patterns("__pycache__", "*.pyc"),
            )
            environment = dict(os.environ)
            environment.pop("PYTHONDONTWRITEBYTECODE", None)
            process = subprocess.run(
                [sys.executable, str(package / "tools" / "verify.py"), "--help"],
                cwd=package,
                env=environment,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=30,
                check=False,
            )
            self.assertEqual(0, process.returncode, process.stderr)
            self.assertEqual([], list(package.rglob("*.pyc")))
            self.assertEqual([], [path for path in package.rglob("__pycache__")])

    def load(self, root, change=None):
        import verify
        package, manifest, policy = fixture_pack(root, change)
        verify.POLICY_CONTRACT = frozenset((len(item), hashlib.sha256(item.encode()).hexdigest())
                                           for item in json.loads(policy.read_text())["blocked"])
        raw = json.loads(manifest.read_text())
        rows = sorted((item["module"], item["name"], item["kind"]) for item in raw["declarations"])
        verify.DECLARATION_CONTRACT_SHA256 = hashlib.sha256(json.dumps(rows, separators=(",", ":")).encode()).hexdigest()
        verify.KIND_TOTALS = {"theorem": 203}
        claim_rows = json.loads((package / "CLAIM_MAP.json").read_text())["claims"]
        verify.CLAIM_ENDPOINT_SET_SHA256 = hashlib.sha256(verify._contract_bytes(sorted({endpoint for row in claim_rows for endpoint in row["endpoints"]}))).hexdigest()
        verify.CLAIM_ROWS_SHA256 = hashlib.sha256(verify._contract_bytes([(row["id"], row["kind"], tuple(row["endpoints"])) for row in claim_rows])).hexdigest()
        raw["kind_totals"] = verify.KIND_TOTALS
        manifest.write_text(json.dumps(raw))
        return package, verify.load_config(manifest, policy)

    def assert_rejected(self, root, expected, change=None):
        from verify import VerificationError, preflight
        with self.assertRaisesRegex(VerificationError, expected):
            _, config = self.load(root, change)
            preflight(config)

    def test_rejects_bad_schema(self):
        with tempfile.TemporaryDirectory() as raw:
            self.assert_rejected(Path(raw), "schema", lambda _, c, __: c.update(schema_version=7))

    def test_rejects_boolean_schema_versions_in_public_contracts(self):
        with tempfile.TemporaryDirectory() as raw:
            def change_claim(package, config, _):
                path = package / "CLAIM_MAP.json"
                claim_map = json.loads(path.read_text())
                claim_map["schema_version"] = True
                path.write_text(json.dumps(claim_map), encoding="utf-8")
                for row in config["public_files"]:
                    if row["path"] == "CLAIM_MAP.json":
                        row.update(sha256=digest(path), bytes=path.stat().st_size)
            self.assert_rejected(Path(raw), "claim map schema", change_claim)
        with tempfile.TemporaryDirectory() as raw:
            def change_dependencies(package, config, _):
                path = package / "DEPENDENCIES.json"
                dependencies = json.loads(path.read_text())
                dependencies["schema_version"] = True
                path.write_text(json.dumps(dependencies), encoding="utf-8")
                for row in config["public_files"]:
                    if row["path"] == "DEPENDENCIES.json":
                        row.update(sha256=digest(path), bytes=path.stat().st_size)
            self.assert_rejected(Path(raw), "dependency pins", change_dependencies)

    def test_claim_map_requires_exact_endpoint_contract(self):
        with tempfile.TemporaryDirectory() as raw:
            def change(package, config, _):
                path = package / "CLAIM_MAP.json"
                raw_map = json.loads(path.read_text())
                raw_map["claims"][0]["endpoints"][0] = "ArithmeticClock.not_selected"
                path.write_text(json.dumps(raw_map), encoding="utf-8")
                for row in config["public_files"]:
                    if row["path"] == "CLAIM_MAP.json":
                        row.update(sha256=digest(path), bytes=path.stat().st_size)
            self.assert_rejected(Path(raw), "claim map", change)

    def test_rejects_unknown_schema_key_and_manifest_control_marker(self):
        with tempfile.TemporaryDirectory() as raw:
            self.assert_rejected(Path(raw), "unknown", lambda _, c, __: c.update(unreviewed=True))
        with tempfile.TemporaryDirectory() as raw:
            def change(_, config, __):
                config["negative_controls"][0]["expect_any"] = ["anything"]
            self.assert_rejected(Path(raw), "control", change)

    def test_rejects_empty_or_replaced_external_policy(self):
        import verify
        with tempfile.TemporaryDirectory() as raw:
            package, manifest, policy = fixture_pack(Path(raw))
            policy.write_text(json.dumps({"schema_version": 1, "blocked": []}))
            with self.assertRaisesRegex(verify.VerificationError, "policy contract"):
                verify.load_config(manifest, policy)
            self.assertFalse(policy.is_relative_to(package))

    def test_rejects_source_hash_mismatch(self):
        with tempfile.TemporaryDirectory() as raw:
            def change(package, _, __):
                next((package / "ArithmeticClock").rglob("*.lean")).write_text("namespace ArithmeticClock\nend ArithmeticClock\n")
            self.assert_rejected(Path(raw), "hash", change)

    def test_rejects_extra_module_and_import(self):
        def extra_module(package, _, __):
            (package / "ArithmeticClock" / "Extra.lean").write_text(
                "namespace ArithmeticClock\nend ArithmeticClock\n")

        def changed_import(package, config, _):
            target = package / config["modules"][0]["source"]
            target.write_text(target.read_text() + "import ArithmeticClock.Extra\n")

        cases = (
            (extra_module, "unbound public package member"),
            (changed_import, "public input hash mismatch"),
        )
        for change, expected in cases:
            with self.subTest(change=change.__name__), tempfile.TemporaryDirectory() as raw:
                self.assert_rejected(Path(raw), expected, change)

    def test_external_policy_token_is_rejected(self):
        with tempfile.TemporaryDirectory() as raw:
            def change(package, config, policy):
                target = package / config["modules"][0]["source"]
                target.write_text(target.read_text() + "\n-- __policy_probe__")
                config["modules"][0]["sha256"] = digest(target)
            self.assert_rejected(Path(raw), "forbidden public token", change)

    def test_json_privacy_scan_uses_decoded_unicode_semantics(self):
        import verify
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            _, config = self.load(root / "fixture")
            encoded = verify._canonical({"literal_types": {
                "decl": "∀ (z : ℂ), z → z"}})
            self.assertIn((chr(92) + "u2200").encode("ascii"), encoded)
            try:
                verify._privacy_scan(config, root / "certificate.json", encoded)
            except verify.VerificationError as raised:
                self.fail("canonical Unicode JSON was path-scanned as encoded text: " + str(raised))

    def test_json_privacy_scan_rejects_escaped_semantic_findings(self):
        import verify
        slash, backslash = chr(47), chr(92)

        def escaped_document(value):
            escaped = "".join(backslash + "u" + format(ord(char), "04x") for char in value)
            return ("{" + json.dumps("value") + ":" + json.dumps(escaped) + "}").replace(
                backslash * 2 + "u", backslash + "u").encode("ascii")

        findings = (
            (slash + "private" + slash + "build" + slash + "Main.lean", "absolute host path"),
            ("C:" + backslash + "Users" + backslash + "alice" + backslash + "Main.lean", "absolute host path"),
            (backslash * 2 + "server" + backslash + "share" + backslash + "Main.lean", "absolute host path"),
            ("s" + "sh" + chr(58) + slash * 2 + "host" + slash + "repository", "absolute host path"),
            ("__policy_probe__", "forbidden public token"),
            ("\0", "NUL"),
        )
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            _, config = self.load(root / "fixture")
            target = root / "probe.json"
            for value, expected in findings:
                with self.subTest(value=repr(value)), self.assertRaisesRegex(
                        verify.VerificationError, expected):
                    verify._privacy_scan(config, target, escaped_document(value))

    def test_json_privacy_scan_rejects_malformed_duplicate_and_nonfinite_documents(self):
        import verify
        documents = (
            (b'{"value":', "invalid JSON"),
            (b'{"value":"one","value":"two"}', "duplicate JSON key"),
            (b'{"value":NaN}', "nonfinite JSON number"),
            (b'{"value":1e999}', "nonfinite JSON number"),
            (b'{"value":-1e999}', "nonfinite JSON number"),
        )
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            _, config = self.load(root / "fixture")
            target = root / "probe.json"
            for document, expected in documents:
                with self.subTest(document=document), self.assertRaisesRegex(
                        verify.VerificationError, expected):
                    verify._privacy_scan(config, target, document)

    def test_json_privacy_scan_accepts_finite_exponent(self):
        import verify
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            _, config = self.load(root / "fixture")
            verify._privacy_scan(config, root / "probe.json", b'{"value":1e99}')

    def test_scanner_ignores_comments_and_strings_but_rejects_command(self):
        from pack_common import scan_lean
        scan_lean(chr(47) + "- sorry -" + chr(47) + chr(10) + "#check \"admit\"" + chr(10))
        with self.assertRaisesRegex(ValueError, "unsafe production token"):
            scan_lean("example : True := by exact True.intro\n" + "run" + "_cmd #check True")

    def test_preflight_accepts_exact_closure_and_rejects_absolute_content(self):
        from verify import VerificationError, preflight
        with tempfile.TemporaryDirectory() as raw:
            package, config = self.load(Path(raw))
            self.assertEqual(__import__("pack_common").BUILD_ORDER, tuple(preflight(config)))
            target = package / config.modules[0].source
            target.write_text(target.read_text() + "\n-- " + chr(47) + "host/secret\n")
            with self.assertRaisesRegex(VerificationError, "absolute host path"):
                preflight(config)

    def test_public_tree_is_exact_and_url_text_is_not_a_host_path(self):
        from verify import VerificationError, preflight
        from pack_common import has_absolute_host_path
        self.assertTrue(has_absolute_host_path("prefix=" + chr(47) + "-secret/location"))
        self.assertFalse(has_absolute_host_path("https://example.invalid/path"))
        self.assertTrue(has_absolute_host_path("fi" + "le:" + chr(47) * 3 + "private/location"))
        with tempfile.TemporaryDirectory() as raw:
            package, config = self.load(Path(raw))
            (package / "LICENSE").write_text("see http://www.apache.org/licenses/LICENSE-2.0\n")
            with self.assertRaisesRegex(VerificationError, "public input hash"):
                preflight(config)
            (package / "LICENSE").write_text("fixture LICENSE\n")
            target = package / config.modules[0].source
            target.write_text(target.read_text() + "\n-- https://example.invalid/path\n")
            object.__setattr__(config.modules[0], "sha256", digest(target))
            object.__setattr__(config.modules[0], "bytes", target.stat().st_size)
            rebind_public(config, config.modules[0].source, target)
            self.assertEqual(set(NAMES), set(preflight(config)))

    def test_host_path_classifier_rejects_all_non_http_uris_and_rooted_windows_forms(self):
        import verify
        from pack_common import has_absolute_host_path, has_compiled_host_path
        slash, backslash = chr(47), chr(92)
        rejected = (
            "cwd=" + slash,
            "working directory: " + slash,
            slash * 2,
            "prefix " + slash * 2 + " suffix",
            "prefix" + chr(10) + slash * 2 + chr(10) + "suffix",
            "source " + slash + "vault end",
            '"' + slash + "a" + '"',
            "s" + "sh:" + slash * 2 + "host/repository",
            "f" + "tp:" + slash * 2 + "host/archive",
            "cust" + "om" + chr(58) + slash * 2 + "host/archive",
            "fi" + "le:" + slash + "private/location",
            "da" + "ta:" + "text/plain,payload",
            "ur" + "n:" + "isbn:example",
            backslash + "folder",
            '"' + backslash + "folder" + '"',
            '"' + backslash + "temp" + '"',
            '"' + backslash + "new" + backslash + "private" + '"',
            backslash + "a" + backslash + "b",
            backslash * 2 + "a" + backslash + "b",
            backslash * 2 + "server" + backslash + "c$",
            backslash * 2 + "?" + backslash + "UNC" + backslash + "server" + backslash + "share",
            backslash * 4 + "server" + backslash * 2 + "share",
            chr(8726) * 2 + "server" + chr(8726) + "share",
            chr(65340) * 2 + "server" + chr(65340) + "share",
            "https:" + slash * 2 + "example.invalid/doc}" + slash + "home/alice",
        )
        for value in rejected:
            with self.subTest(value=value):
                self.assertTrue(has_absolute_host_path(value))
        allowed = (
            "https:" + slash * 2 + "example.invalid/path",
            "http:" + slash * 2 + "example.invalid/path",
            "Note:important", "harmless:True", "x " + slash + "y",
            "theorem q : Nat := x " + slash + "denominator",
            "{x : " + chr(945) + " " + slash * 2 + " p x}",
            "{x : Nat " + slash * 2 + " p x}",
            backslash + "frac{x}{y}",
        )
        for value in allowed:
            with self.subTest(value=value):
                self.assertFalse(has_absolute_host_path(value))

        compiled_allowed = (b"binary noise /a /z9 C:x",
            b"https:" + slash.encode() * 2 + b"home/user",
            b"https:" + slash.encode() * 2 + b"example.invalid/docs/Main.lean",
            b"profile:" + slash.encode() + b"ratio")
        for value in compiled_allowed:
            with self.subTest(value=value):
                self.assertFalse(has_compiled_host_path(value))
        compiled_rejected = (
            b"debug source " + slash.encode() + b"a/b\x00",
            b"cwd:" + slash.encode() + b"a/b\x00",
            b"path:" + slash.encode() + b"alpha/beta\x00",
            b"source:" + slash.encode() + b"data/project/Main.lean\x00",
            b"profile:" + slash.encode() + b"not/a/path\x00",
            b"debug source " + slash.encode() + b"home/alice/project/Main.lean\x00",
            b"debug source " + slash.encode() + b"data/project/Main.lean\x00",
            b"debug source " + slash.encode() + b"alpha/beta\x00",
            b"debug source C:" + backslash.encode() + b"a" + backslash.encode() + b"b\x00",
            b"debug source C:" + slash.encode() + b"a/b\x00",
            b"debug source C:" + backslash.encode() + b"Users" + backslash.encode() + b"alice" + backslash.encode() + b"Main.lean\x00",
            b"debug source " + backslash.encode() * 2 + b"server" + backslash.encode() + b"share" + backslash.encode() + b"Main.lean\x00",
            b"debug source fi" + b"le:" + slash.encode() * 2 + b"host/share/Main.lean\x00",
            b"debug source s" + b"sh:" + slash.encode() * 2 + b"host/repository\x00",
            b"debug source f" + b"tp:" + slash.encode() * 2 + b"host/archive\x00",
            b"debug source cust" + b"om:" + slash.encode() * 2 + b"host/archive\x00",
            b"debug source xhttps:" + slash.encode() * 2 + b"host/repository\x00",
            b"debug source myhttps:" + slash.encode() * 2 + b"host/repo\x00",
            b"debug source da" + b"ta:text/plain,payload\x00",
            b"debug source ur" + b"n:isbn:example\x00",
        )
        for value in compiled_rejected:
            with self.subTest(value=value):
                self.assertTrue(has_compiled_host_path(value))

        valid_opener = slash + "-! documentation -" + slash
        hidden_path = slash + "-!secret" + slash + "location -" + slash
        comment_path = slash + "-! documentation " + slash + "private -" + slash
        string_path = '"' + slash + "private" + '"'
        self.assertFalse(has_absolute_host_path(verify._mask_lean_comment_delimiters(valid_opener)))
        self.assertTrue(has_absolute_host_path(verify._mask_lean_comment_delimiters(hidden_path)))
        self.assertTrue(has_absolute_host_path(verify._mask_lean_comment_delimiters(comment_path)))
        self.assertTrue(has_absolute_host_path(verify._mask_lean_comment_delimiters(string_path)))

    def test_compiled_privacy_scan_invokes_external_strings_with_all_sections(self):
        import verify
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            _, config = self.load(root / "fixture")
            compiled = root / "clean.olean"
            compiled.write_bytes(b"clean compiled object")
            receipt = root / "strings-arguments"
            helper = root / "strings"
            helper.write_text(
                "#!" + chr(47) + "bin" + chr(47) + "sh\n" +
                "if [ \"$#\" -ne 2 ] || [ \"$1\" != \"-a\" ]; then exit 64; fi\n" +
                "printf '%s\\n%s\\n' \"$1\" \"$2\" > \"$STRINGS_RECEIPT\"\n" +
                "printf '%s\\n' 'clean compiled object'\n",
                encoding="utf-8",
            )
            helper.chmod(0o755)
            environment = {"PATH": str(root), "LANG": "C", "LC_ALL": "C",
                           "STRINGS_RECEIPT": str(receipt)}
            with mock.patch.object(verify.os, "defpath", str(root)):
                verify._compiled_privacy_scan(config, compiled, environment)
            self.assertEqual(["-a", str(compiled)], receipt.read_text(encoding="utf-8").splitlines())

    def test_compiled_privacy_scan_fails_closed_for_missing_or_unusable_strings(self):
        import verify
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            _, config = self.load(root / "fixture")
            compiled = root / "clean.olean"
            compiled.write_bytes(b"clean compiled object")
            empty = root / "empty-path"
            empty.mkdir()
            environment = {"PATH": str(empty), "LANG": "C", "LC_ALL": "C"}
            with mock.patch.object(verify.os, "defpath", str(empty)), \
                    self.assertRaisesRegex(verify.VerificationError, "strings helper"):
                verify._compiled_privacy_scan(config, compiled, environment)

            helper = root / "strings"
            helper.write_text("#!" + chr(47) + "bin" + chr(47) + "sh\nexit 9\n", encoding="utf-8")
            helper.chmod(0o755)
            environment["PATH"] = str(root)
            with mock.patch.object(verify.os, "defpath", str(root)), \
                    self.assertRaisesRegex(verify.VerificationError, "strings scan"):
                verify._compiled_privacy_scan(config, compiled, environment)

    def test_compiled_privacy_scan_rejects_forbidden_strings_output(self):
        import verify
        slash = chr(47)
        findings = (
            ("__policy_probe__", "forbidden public token"),
            (slash + "private" + slash + "build" + slash + "Main.lean", "absolute host path"),
        )
        for payload, expected in findings:
            with self.subTest(payload=payload), tempfile.TemporaryDirectory() as raw:
                root = Path(raw)
                _, config = self.load(root / "fixture")
                compiled = root / "clean.olean"
                compiled.write_bytes(b"clean compiled object")
                helper = root / "strings"
                helper.write_text(
                    "#!" + slash + "bin" + slash + "sh\n" +
                    "printf '%s\\n' \"$STRINGS_PAYLOAD\"\n",
                    encoding="utf-8",
                )
                helper.chmod(0o755)
                environment = {"PATH": str(root), "LANG": "C", "LC_ALL": "C",
                               "STRINGS_PAYLOAD": payload}
                with mock.patch.object(verify.os, "defpath", str(root)), \
                        self.assertRaisesRegex(verify.VerificationError, expected):
                    verify._compiled_privacy_scan(config, compiled, environment)

    def test_preflight_rejects_unselected_declaration(self):
        from verify import VerificationError, preflight
        with tempfile.TemporaryDirectory() as raw:
            package, config = self.load(Path(raw))
            target = package / config.modules[0].source
            target.write_text(target.read_text().replace("end ArithmeticClock", "theorem extra : True := True.intro\nend ArithmeticClock"))
            target_hash = digest(target)
            object.__setattr__(config.modules[0], "sha256", target_hash)
            object.__setattr__(config.modules[0], "bytes", target.stat().st_size)
            rebind_public(config, config.modules[0].source, target)
            with self.assertRaisesRegex(VerificationError, "declaration set"):
                preflight(config)

    def test_preflight_rejects_unsupported_and_facade_declarations(self):
        from verify import VerificationError, preflight
        with tempfile.TemporaryDirectory() as raw:
            package, config = self.load(Path(raw))
            target = package / config.modules[0].source
            target.write_text(target.read_text().replace("end " + config.modules[0].name, "opaque hidden : Prop\nend " + config.modules[0].name))
            object.__setattr__(config.modules[0], "sha256", digest(target))
            object.__setattr__(config.modules[0], "bytes", target.stat().st_size)
            rebind_public(config, config.modules[0].source, target)
            with self.assertRaisesRegex(VerificationError, "unsupported"):
                preflight(config)
        with tempfile.TemporaryDirectory() as raw:
            package, config = self.load(Path(raw))
            facade = package / config.facade
            facade.write_text(facade.read_text() + "opaque hidden : Prop\n")
            object.__setattr__(config, "facade_sha256", digest(facade))
            object.__setattr__(config, "facade_bytes", facade.stat().st_size)
            rebind_public(config, config.facade, facade)
            with self.assertRaisesRegex(VerificationError, "declaration-free"):
                preflight(config)

    def test_declaration_parser_accounts_for_split_wrapped_and_unicode_commands(self):
        from verify import VerificationError, _discover_declarations
        namespace = "ArithmeticClock.CyclicCharacters"
        prefix = "set_option autoImplicit false\nnamespace " + namespace + "\n"
        suffix = chr(10) + "end " + namespace + chr(10)
        rejected = (
            "theorem\nsplitName : True := True.intro",
            "theorem " + chr(945) + " : True := True.intro",
            "set_option autoImplicit false in theorem hidden : True := True.intro",
            "omit [Decidable p] in theorem hidden : True := True.intro",
            "set_option pp.all true",
            "set_option\nautoImplicit false",
            "set_option autoImplicit\nfalse",
            "set_option autoImplicit false in\ntheorem hidden : True := True.intro",
            "omit [Fintype " + chr(953) + "] in theorem hidden : True := True.intro",
            "omit\n[Fintype " + chr(953) + "] in\ntheorem hidden : True := True.intro",
            "omit [Fintype " + chr(953) + "] in\ndef hidden : True := True.intro",
            "alias hidden := visible",
            "mutual\ntheorem hidden : True := True.intro\nend",
            "let rec hidden : Nat := 0",
            "irreducible_def hidden : Nat := 0",
            "infix:65 \" <+> \" => hidden",
            "theorem visible : True := by\n  trivial\nwhere\n  hidden : True := True.intro",
        )
        for command in rejected:
            with self.subTest(command=command), self.assertRaisesRegex(VerificationError, "unsupported"):
                _discover_declarations(prefix + command + suffix, namespace)
        accepted = prefix + "omit [Fintype " + chr(953) + "] in\ntheorem visible : True := True.intro" + suffix
        self.assertEqual({(namespace + ".visible", "theorem")}, _discover_declarations(accepted, namespace))

    def test_rejects_stale_object_symlink_absolute_path_and_wrong_namespace(self):
        cases = []
        def stale(package, _, __): (package / "old.olean").write_bytes(b"old")
        def symlink(package, _, __): os.symlink(package / "package.json", package / "ArithmeticClock" / "alias.lean")
        def path(package, config, _): config["modules"][0]["source"] = chr(47) + "host/outside.lean"
        def namespace(package, config, _):
            target = package / config["modules"][0]["source"]
            target.write_text(target.read_text().replace("namespace " + config["modules"][0]["module"], "namespace Other"))
            config["modules"][0]["sha256"] = digest(target)
            config["modules"][0]["bytes"] = target.stat().st_size
            for row in config["public_files"]:
                if row["path"] == config["modules"][0]["source"]:
                    row.update(sha256=digest(target), bytes=target.stat().st_size)
        cases.extend((stale, symlink, path, namespace))
        for change in cases:
            with self.subTest(change=change.__name__), tempfile.TemporaryDirectory() as raw:
                self.assert_rejected(Path(raw), "object|symlink|source|namespace", change)

    def test_declaration_and_axiom_gates(self):
        from verify import VerificationError, parse_audit, validate_audit
        with tempfile.TemporaryDirectory() as raw:
            _, config = self.load(Path(raw))
            names = [item.name for item in config.declarations]
            with self.assertRaisesRegex(VerificationError, "declaration"):
                validate_audit(config, {name: ("True", []) for name in names[:-1]})
            audit = {name: ("True", []) for name in names}
            audit[names[0]] = ("True", ["bad.axiom"])
            with self.assertRaisesRegex(VerificationError, "axiom"):
                validate_audit(config, audit)
            def record(item, literal="True"):
                declaration = next(value for value in config.declarations if value.name == item)
                return "\n".join(("\"__AUDIT_BEGIN " + item + "\" : String",
                                  declaration.kind + " " + item,
                                  "\"__AUDIT_KIND_END " + item + "\" : String",
                                  "@" + item + " : " + literal,
                                  "\"__AUDIT_TYPE_END " + item + "\" : String",
                                  "'" + item + "' does not depend on any axioms",
                                  "\"__AUDIT_AXIOM_END " + item + "\" : String",
                                  "\"__AUDIT_END " + item + "\" : String"))
            rendered = "\n".join(record(name) for name in names)
            self.assertEqual(set(names), set(parse_audit(config, rendered)))
            overlap = record(names[0], "A") + "\n" + record(names[1], "B")
            overlap = overlap.replace("\"__AUDIT_END " + names[0] + "\" : String", "")
            overlap += "\n" + "\n".join(record(name) for name in names[2:])
            with self.assertRaisesRegex(VerificationError, "framed|overlapping"):
                parse_audit(config, overlap)
            with self.assertRaisesRegex(VerificationError, "order|unparsed|framed"):
                parse_audit(config, "garbage\n" + rendered)
            records = [record(name) for name in names]
            with self.assertRaisesRegex(VerificationError, "order|unparsed|framed"):
                parse_audit(config, records[0] + chr(10) + "inter-record garbage" + chr(10) +
                            chr(10).join(records[1:]))
            first = names[0]
            multiline_universe = rendered.replace(
                "theorem " + first, "theorem " + first + ".{u_1,\n u_2}", 1).replace(
                "@" + first + " :", "@" + first + ".{u_1,\n u_2} :", 1)
            self.assertIn(first, parse_audit(config, multiline_universe))
            malformed_universe = rendered.replace("theorem " + first, "theorem " + first + ".{u_1,,u_2}", 1)
            with self.assertRaisesRegex(VerificationError, "kind evidence"):
                parse_audit(config, malformed_universe)
            replace = __import__("dataclasses").replace
            first_declaration = config.declarations[0]
            false_def_contract = replace(config, declarations=(replace(first_declaration, kind="def"),
                *config.declarations[1:]), kind_totals=None)
            reducible_output = rendered.replace("theorem " + first, "@[reducible] def " + first, 1)
            with self.assertRaisesRegex(VerificationError, "kind differs"):
                parse_audit(false_def_contract, reducible_output)
            injected_marker = rendered.replace(
                "\"__AUDIT_KIND_END " + first,
                "__AUDIT_FAKE " + first + chr(10) + "\"__AUDIT_KIND_END " + first, 1)
            with self.assertRaisesRegex(VerificationError, "kind evidence|phase|framed"):
                parse_audit(config, injected_marker)

    def test_controls_require_markers(self):
        import verify
        from verify import VerificationError, validate_control
        with self.assertRaisesRegex(VerificationError, "diagnostic class"):
            validate_control("wrong_period", 1, "unknown identifier", ("0 = 0", "30 = 0"))
        transcript = "Control.lean" + chr(58) + "1:1: error: type mismatch\n0 = 0\nhas type\n0 = 0\nbut is expected to have type\n30 = 0\n"
        previous = verify.CONTROL_DIGESTS
        try:
            verify.CONTROL_DIGESTS = {"invalid_false": "0" * 64,
                "wrong_period": hashlib.sha256(b"<file>: error: type mismatch\n0 = 0\nhas type\n0 = 0\nbut is expected to have type\n30 = 0\n").hexdigest()}
            evidence = validate_control("wrong_period", 1, transcript, ("0 = 0", "30 = 0"))
            self.assertEqual("PASS", evidence["status"])
            with self.assertRaisesRegex(VerificationError, "crashed"):
                validate_control("wrong_period", -11, transcript, ("0 = 0", "30 = 0"))
            with self.assertRaisesRegex(VerificationError, "diagnostic class"):
                validate_control("wrong_period", 1, transcript + "\n", ("0 = 0", "30 = 0"))
            with self.assertRaisesRegex(VerificationError, "diagnostic class"):
                validate_control("wrong_period", 1, transcript + "trailing\n", ("0 = 0", "30 = 0"))
        finally:
            verify.CONTROL_DIGESTS = previous

    def test_dependency_scans_reject_same_root_casefold_collisions_and_duplicate_rows(self):
        import verify
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            _, config = self.load(root / "fixture")
            lean = root / "lean"
            lean.write_bytes(b"compiler")
            evidence = {"sha256": digest(lean), "bytes": lean.stat().st_size}
            source = root / "source" / "Source.lean"
            source.parent.mkdir()
            source.write_text("import Mathlib.Tactic\n", encoding="utf-8")
            binding = (digest(source), source.stat().st_size)
            build, external = root / "build", root / "external"
            build.mkdir(); external.mkdir()
            upper, lower = external / "Alpha.olean", external / "alpha.olean"
            upper.write_bytes(b"upper"); lower.write_bytes(b"lower")
            with mock.patch.object(verify, "_run", return_value=str(upper) + "\n"):
                with self.assertRaisesRegex(verify.VerificationError, "case-fold|duplicate relative"):
                    verify._check_deps(lean, evidence, config, source, *binding, "dependency source",
                                       root, {}, build, (("@mathlib", external),))
            lower.unlink()
            with mock.patch.object(verify, "_run", return_value=str(upper) + "\n" + str(upper) + "\n"):
                with self.assertRaisesRegex(verify.VerificationError, "duplicate compiler dependency"):
                    verify._check_deps(lean, evidence, config, source, *binding, "dependency source",
                                       root, {}, build, (("@mathlib", external),))

    def test_exact_lake_manifest_dependency_rows_remain_accepted(self):
        import verify
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            mathlib = root / "mathlib"
            rows = []
            for name in verify.DEPENDENCY_ORDER:
                url, scope, input_rev, inherited, config_file = verify.DEPENDENCY_ROWS[name]
                rows.append({"url": url, "type": "git", "subDir": None, "scope": scope,
                    "rev": verify.DEPENDENCY_PINS[name], "name": name, "inputRev": input_rev,
                    "inherited": inherited, "manifestFile": "lake-manifest.json",
                    "configFile": config_file})
                (mathlib / ".lake" / "packages" / name / ".lake" / "build" / "lib" / "lean").mkdir(
                    parents=True)
            manifest = mathlib / "lake-manifest.json"
            manifest.write_text(json.dumps({"version": "1.1.0", "name": "mathlib", "lakeDir": ".lake",
                "packagesDir": ".lake/packages", "packages": rows}), encoding="utf-8")

            def git_result(argv, *_args, **_kwargs):
                if "rev-parse" in argv:
                    checkout = Path(argv[argv.index("-C") + 1])
                    return verify.DEPENDENCY_PINS[checkout.name] + "\n"
                return ""

            with mock.patch.object(verify, "MATHLIB_MANIFEST_SHA256", digest(manifest)), \
                    mock.patch.object(verify, "_run", side_effect=git_result):
                caches, revisions = verify._dependency_caches(mathlib, root / "git", root, {})
            self.assertEqual(list(verify.DEPENDENCY_PINS.items()), list(revisions.items()))
            self.assertEqual(["@dependency/" + name for name in verify.DEPENDENCY_ORDER],
                             [logical for logical, _ in caches])

    def test_bound_lean_input_uses_verified_stdin_snapshot_and_neutral_root(self):
        import verify
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            _, config = self.load(root / "fixture")
            source = root / "source" / "ArithmeticClock" / "Probe.lean"
            source.parent.mkdir(parents=True)
            original = "example : True := True.intro\n"
            source.write_text(original, encoding="utf-8")
            binding = (digest(source), source.stat().st_size)
            lean = root / "lean"
            lean.write_bytes(b"compiler")
            evidence = {"sha256": digest(lean), "bytes": lean.stat().st_size}
            captured = {}

            def mutate_after_snapshot(argv, cwd, env, expect_failure=False, input_text=None):
                captured.update(argv=argv, input_text=input_text)
                source.write_text("example : False := False.elim (by contradiction)\n", encoding="utf-8")
                return ""

            with mock.patch.object(verify, "_run", side_effect=mutate_after_snapshot):
                with self.assertRaisesRegex(verify.VerificationError, "probe source changed"):
                    verify._run_bound_lean(config, lean, evidence, source, *binding, "probe source",
                                           ["--deps"], root, {})
            self.assertEqual(original, captured["input_text"])
            self.assertEqual([str(lean), "--deps", "--root=source", "--stdin",
                              "source/ArithmeticClock/Probe.lean"], captured["argv"])

    def test_object_build_uses_private_fifo_with_exact_bytes_and_module_path(self):
        import verify
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            _, config = self.load(root / "fixture")
            run = root / "run"
            build = run / "build" / "ArithmeticClock"
            build.mkdir(parents=True)
            lean = root / "fake-lean"
            slash = chr(47)
            program = """import json, os, pathlib, stat, sys
args = sys.argv[1:]
pathlib.Path(os.environ[\"FIFO_ARGS\"]).write_text(json.dumps(args))
info = os.stat(args[-1])
assert stat.S_ISFIFO(info.st_mode)
assert info.st_mode & 0o777 == 0o600
assert os.stat(pathlib.Path(args[-1]).parents[1]).st_mode & 0o777 == 0o700
with open(args[-1], \"rb\") as incoming:
    payload = incoming.read()
pathlib.Path(os.environ[\"FIFO_RECEIPT\"]).write_bytes(payload)
target = pathlib.Path(args[args.index(\"-o\") + 1])
target.parent.mkdir(parents=True, exist_ok=True)
target.write_bytes(b\"object\")
"""
            lean.write_text("#!" + slash + "usr" + slash + "bin" + slash + "env python3\n" + program,
                            encoding="utf-8")
            lean.chmod(0o755)
            evidence = {"sha256": digest(lean), "bytes": lean.stat().st_size}
            env = os.environ.copy()
            env["FIFO_ARGS"] = str(root / "argv.json")
            env["FIFO_RECEIPT"] = str(root / "receipt.bin")
            final_source = None
            final_binding = None
            for index, module in enumerate(__import__("pack_common").BUILD_ORDER):
                leaf = module.rsplit(".", 1)[1]
                source = run / "source" / "ArithmeticClock" / (leaf + ".lean")
                source.parent.mkdir(parents=True, exist_ok=True)
                original = (b"-- backpressure probe\n" + b"x" * (256 * 1024) + b"\n") if index == 0 else \
                    ("example " + leaf.lower() + " : True := True.intro\n").encode()
                source.write_bytes(original)
                binding = (digest(source), source.stat().st_size)
                object_name = "build/ArithmeticClock/" + leaf + ".olean"
                arguments = ["-DwarningAsError=true", "-o", object_name]
                if index == 0:
                    real_open, real_write = verify.os.open, verify.os.write
                    interrupted = {"open": False, "write": False}
                    def flaky_open(path, flags, *args):
                        if flags & os.O_WRONLY and not interrupted["open"]:
                            interrupted["open"] = True
                            raise InterruptedError(4, "interrupted")
                        return real_open(path, flags, *args)
                    def flaky_write(descriptor, payload):
                        if not interrupted["write"]:
                            interrupted["write"] = True
                            raise InterruptedError(4, "interrupted")
                        return real_write(descriptor, payload)
                    with mock.patch.object(verify.os, "open", side_effect=flaky_open), \
                            mock.patch.object(verify.os, "write", side_effect=flaky_write):
                        transcript = verify._run_fifo_lean(config, lean, evidence, source, *binding,
                            "probe source", arguments, run, env)
                    self.assertEqual({"open": True, "write": True}, interrupted)
                else:
                    transcript = verify._run_fifo_lean(config, lean, evidence, source, *binding,
                        "probe source", arguments, run, env)
                self.assertEqual("", transcript)
                self.assertEqual(original, (root / "receipt.bin").read_bytes())
                self.assertEqual(["-DwarningAsError=true", "-o", object_name,
                                  "--root=feed", "feed/ArithmeticClock/" + leaf + ".lean"],
                                 json.loads((root / "argv.json").read_text()))
                self.assertEqual(b"object", (build / (leaf + ".olean")).read_bytes())
                self.assertFalse((run / "feed").exists())
                final_source, final_binding = source, binding

            with mock.patch.object(verify.os, "mkfifo", side_effect=NotImplementedError):
                with self.assertRaisesRegex(verify.VerificationError, "named FIFO"):
                    verify._run_fifo_lean(config, lean, evidence, final_source, *final_binding, "probe source",
                        ["-o", "build/ArithmeticClock/IntegerClock60.olean"], run, env)
            self.assertFalse((run / "feed").exists())

            lean.write_text("#!" + slash + "usr" + slash + "bin" + slash + "env python3\n",
                            encoding="utf-8")
            lean.chmod(0o755)
            evidence = {"sha256": digest(lean), "bytes": lean.stat().st_size}
            with self.assertRaisesRegex(verify.VerificationError, "delivery was incomplete"):
                verify._run_fifo_lean(config, lean, evidence, final_source, *final_binding, "probe source",
                    ["-o", "build/ArithmeticClock/IntegerClock60.olean"], run, env)
            self.assertFalse((run / "feed").exists())

            lean.write_text("#!" + slash + "usr" + slash + "bin" + slash + "env python3\n" +
                            "raise SystemExit(7)\n", encoding="utf-8")
            lean.chmod(0o755)
            evidence = {"sha256": digest(lean), "bytes": lean.stat().st_size}
            with mock.patch.object(verify.VerificationError, "add_note", None, create=True):
                try:
                    verify._run_fifo_lean(config, lean, evidence, final_source, *final_binding, "probe source",
                        ["-o", "build/ArithmeticClock/IntegerClock60.olean"], run, env)
                except verify.VerificationError as raised:
                    self.assertRegex(str(raised), "subprocess exit behavior")
                    self.assertTrue(any("secondary FIFO failure" in note
                                        for note in raised.__notes__))
                except BaseException as raised:
                    self.fail("secondary FIFO handling masked the primary failure with " + repr(raised))
                else:
                    self.fail("expected the primary compiler failure")
            self.assertFalse((run / "feed").exists())

    def test_build_and_certificate_logical_paths_are_exact_and_casefold_unique(self):
        import verify
        objects = {logical: "1" * 64 for logical in verify._expected_objects()}
        base = {"status": "PASS", "lean": "@lean", "mathlib": "@mathlib",
                "manifest": "@mathlib/lake-manifest.json", "objects": objects,
                "direct_dependencies": {"@mathlib/Mathlib/Tactic.olean": "2" * 64,
                                        "@lean/Init.olean": "3" * 64},
                "dependency_evidence_scope": "lean-direct-import-objects-only",
                "external_cache_boundary": "pinned-checkouts-with-prebuilt-objects-reused",
                "dependency_revisions": dict(verify.DEPENDENCY_PINS), "external_caches_reused": True,
                "compiler": {"sha256": "4" * 64, "bytes": 1},
                "mathlib_manifest": {"sha256": verify.MATHLIB_MANIFEST_SHA256, "bytes": 1}}
        verify._validate_build_evidence(base)
        for dependency in ("@mathlib/Mathlib/Tactic.ilean", "@dependency/notPinned/Thing.olean"):
            changed = {**base, "direct_dependencies": {dependency: "2" * 64, "@lean/Init.olean": "3" * 64}}
            with self.subTest(dependency=dependency), self.assertRaisesRegex(
                    verify.VerificationError, "dependency logical identity"):
                verify._validate_build_evidence(changed)
        colliding = {**base, "direct_dependencies": {
            "@mathlib/Mathlib/Tactic.olean": "2" * 64,
            "@mathlib/mathlib/tactic.olean": "2" * 64,
            "@lean/Init.olean": "3" * 64}}
        with self.assertRaisesRegex(verify.VerificationError, "case-fold"):
            verify._validate_build_evidence(colliding)

        verify._validate_certificate_paths({"paths": ["@package", "@package/file.txt", "@run/build/file.olean",
            "@lean/Init.olean", "@mathlib/Mathlib/Tactic.olean", "@dependency/Qq/Qq/Thing.olean"]})
        for logical in ("@dependencyevil/file.olean", "@dependency/notPinned/file.olean", "@unknown/file"):
            with self.subTest(logical=logical), self.assertRaisesRegex(
                    verify.VerificationError, "unknown logical path"):
                verify._validate_certificate_paths({"path": logical})

    def test_certificate_path_gate_distinguishes_lean_explicit_arguments(self):
        import verify
        literals = (EXPLICIT_ARGUMENT_LITERAL, "@Eq.{1} Nat 1 1", "@Units.val Nat instMonoidNat")
        for literal in literals:
            document = {
                "literal_types": {
                    "ArithmeticClock.CyclicTwirl.weights60_injective": literal,
                },
                "type_axiom_artifact": {"path": "@run/types-and-axioms.txt"},
            }
            try:
                verify._validate_certificate_paths(document)
            except verify.VerificationError as raised:
                self.fail("Lean explicit-argument syntax was classified as a logical path: " + str(raised))

        document["type_axiom_artifact"]["path"] = "@unknown/types-and-axioms.txt"
        with self.assertRaisesRegex(verify.VerificationError, "unknown logical path"):
            verify._validate_certificate_paths(document)

    def test_certificate_path_gate_does_not_exempt_malformed_literal_fields(self):
        import verify
        malformed = (
            {"literal_types": ["@unknown/hidden"]},
            {"literal_types": {"decl": {"path": "@unknown/hidden"}}},
            {"wrapper": {"literal_types": {"decl": "@unknown/hidden"}}},
            {"literal_types": {"@unknown/hidden": "True"}},
        )
        for document in malformed:
            with self.subTest(document=document), self.assertRaisesRegex(
                    verify.VerificationError, "unknown logical path"):
                verify._validate_certificate_paths(document)

    def test_certificate_path_gate_rejects_path_shaped_direct_literal_value(self):
        import verify
        for whitespace in (" ", "\t", "\n"):
            with self.subTest(whitespace=repr(whitespace)), self.assertRaisesRegex(
                    verify.VerificationError, "unknown logical path"):
                verify._validate_certificate_paths(
                    {"literal_types": {"decl": whitespace + "@unknown/hidden"}})

    def test_certificate_path_gate_keeps_literal_type_string_safety_checks(self):
        import verify
        slash, backslash = chr(47), chr(92)
        unsafe = (
            EXPLICIT_ARGUMENT_LITERAL + "\0",
            EXPLICIT_ARGUMENT_LITERAL + backslash + "host",
            EXPLICIT_ARGUMENT_LITERAL + "\n" + slash + "private" + slash + "build" + slash + "Main.lean",
            EXPLICIT_ARGUMENT_LITERAL + "\n" + "fi" + "le" + chr(58) + slash + "private" + slash + "Main.lean",
        )
        for literal in unsafe:
            with self.subTest(literal=literal), self.assertRaisesRegex(
                    verify.VerificationError, "nonlogical path"):
                verify._validate_certificate_paths({"literal_types": {"decl": literal}})

    def test_compiler_invocations_are_guarded_before_and_after_execution(self):
        import verify
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            lean = root / "lean"
            shutil.copy2(sys.executable, lean)
            evidence = {"sha256": digest(lean), "bytes": lean.stat().st_size}
            lean.write_bytes(lean.read_bytes() + b"changed")
            with self.assertRaisesRegex(verify.VerificationError, "before invocation"):
                verify._run_lean(lean, evidence, ["-c", "pass"], root, os.environ.copy())

            lean.write_text("#!" + chr(47) + "bin" + chr(47) + "sh\nmv \"$0.new\" \"$0\"\n", encoding="utf-8")
            lean.chmod(0o755)
            replacement = lean.with_name("lean.new")
            replacement.write_text("replaced\n", encoding="utf-8")
            replacement.chmod(0o755)
            evidence = {"sha256": digest(lean), "bytes": lean.stat().st_size}
            with self.assertRaisesRegex(verify.VerificationError, "after invocation"):
                verify._run_lean(lean, evidence, [], root, os.environ.copy())

    def test_special_files_are_rejected_before_any_blocking_read(self):
        import verify
        special = Path(chr(47) + "dev" + chr(47) + "null")
        if not special.exists():
            self.skipTest("no harmless special-file fixture")
        with tempfile.TemporaryDirectory() as raw:
            package, config = self.load(Path(raw))
            with mock.patch.object(Path, "read_bytes", side_effect=AssertionError("must not read")):
                with self.assertRaisesRegex(verify.VerificationError, "changed"):
                    verify._read_relocated_input(config, special, "0" * 64, 1, "special source")
            with mock.patch.object(verify, "sha256_file", side_effect=AssertionError("must not hash")):
                with self.assertRaisesRegex(verify.VerificationError, "compiler changed"):
                    verify._guard_compiler(special, {"sha256": "0" * 64, "bytes": 1}, "before invocation")
            pin = package / "lean-toolchain"
            pin.unlink()
            os.mkfifo(pin)
            with mock.patch.object(Path, "read_bytes", side_effect=AssertionError("must not read")):
                with self.assertRaisesRegex(verify.VerificationError, "toolchain pin"):
                    verify._validate_public_pins(package)

    def test_relocated_bindings_and_full_ancestor_closure_are_enforced(self):
        import verify
        self.assertEqual({"a", "a/b", "x", "x/y", "x/y/z"},
                         verify._ancestor_directories({"a/b/file", "x/y/z/value"}))
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            _, config = self.load(root)
            target = root / "relocated.lean"
            target.write_text("example : True := True.intro\n", encoding="utf-8")
            expected = (digest(target), target.stat().st_size)
            verify._check_relocated_input(config, target, *expected, "generated source")
            target.write_text(target.read_text() + "-- changed\n", encoding="utf-8")
            with self.assertRaisesRegex(verify.VerificationError, "generated source changed"):
                verify._check_relocated_input(config, target, *expected, "generated source")

    def test_logical_deterministic_atomic_certificates(self):
        from verify import VerificationResult, emit_certificates
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            _, config = self.load(root)
            build = root / "fresh-build"
            objects = {}
            for module in NAMES:
                target = build / Path(*module.split(".")).with_suffix(".olean")
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(b"verified object")
                objects["@run/build/" + target.relative_to(build).as_posix()] = digest(target)
            result = VerificationResult(config=config, module_order=list(__import__("pack_common").BUILD_ORDER), audit={
                item.name: ("True", []) for item in config.declarations}, controls={name: {"status": "PASS", "diagnostic_class": "lean-4.19-type-mismatch", "normalized_sha256": value} for name, value in __import__("verify").CONTROL_DIGESTS.items()},
                build={"status": "PASS", "lean": "@lean", "mathlib": "@mathlib", "manifest": "@mathlib/lake-manifest.json", "objects": objects,
                       "direct_dependencies": {"@mathlib/Mathlib/Tactic.olean": "2" * 64, "@lean/Init.olean": "4" * 64},
                       "dependency_evidence_scope": "lean-direct-import-objects-only",
                       "external_cache_boundary": "pinned-checkouts-with-prebuilt-objects-reused",
                       "dependency_revisions": __import__("verify").DEPENDENCY_PINS,
                       "external_caches_reused": True, "compiler": {"sha256": "3" * 64, "bytes": 1},
                       "mathlib_manifest": {"sha256": __import__("verify").MATHLIB_MANIFEST_SHA256, "bytes": 1}})
            first = emit_certificates(result, root / "one", build)
            second = emit_certificates(result, root / "two", build)
            self.assertEqual([p.read_bytes() for p in first], [p.read_bytes() for p in second])
            for path in first:
                self.assertNotIn(str(root).encode(), path.read_bytes())
                self.assertEqual("PASS", json.loads(path.read_text())["status"])
            build_certificate = json.loads((root / "one" / "certificates" / "BUILD_CERTIFICATE.json").read_text())
            self.assertEqual({"lean", "mathlib", "manifest"}, set(build_certificate["paths"]))
            self.assertIn("direct_dependencies", build_certificate)
            self.assertNotIn("dependencies", build_certificate)
            failing = VerificationResult(config=config, module_order=[], audit={}, controls={}, build={"status": "FAIL"})
            with self.assertRaises(Exception):
                emit_certificates(failing, root / "fail")
            self.assertFalse((root / "fail" / "certificates").exists())
            unsafe = VerificationResult(config=config, module_order=list(__import__("pack_common").BUILD_ORDER), audit={
                item.name: ("True", []) for item in config.declarations}, controls={name: {"status": "PASS", "diagnostic_class": "lean-4.19-type-mismatch", "normalized_sha256": value} for name, value in __import__("verify").CONTROL_DIGESTS.items()},
                build={"status": "PASS", "lean": "ur" + "n" + chr(58) + "host", "mathlib": "@mathlib", "manifest": "@mathlib/lake-manifest.json", "objects": objects,
                       "direct_dependencies": {"@mathlib/Mathlib/Tactic.olean": "2" * 64, "@lean/Init.olean": "4" * 64},
                       "dependency_evidence_scope": "lean-direct-import-objects-only",
                       "external_cache_boundary": "pinned-checkouts-with-prebuilt-objects-reused",
                       "dependency_revisions": __import__("verify").DEPENDENCY_PINS,
                       "external_caches_reused": True, "compiler": {"sha256": "3" * 64, "bytes": 1},
                       "mathlib_manifest": {"sha256": __import__("verify").MATHLIB_MANIFEST_SHA256, "bytes": 1}})
            with self.assertRaisesRegex(Exception, "build evidence|nonlogical"):
                emit_certificates(unsafe, root / "unsafe", build)


def certified_release_fixture(root):
    """Create verifier-issued artifacts around the synthetic public test package."""
    import verify
    package, config = VerifierTests().load(root)
    build = root / "fresh-build"
    objects = {}
    for module in NAMES:
        target = build / Path(*module.split(".")).with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(b"verified-object-" + module.rsplit(".", 1)[1].encode("ascii"))
        objects["@run/build/" + target.relative_to(build).as_posix()] = digest(target)
    audit = {item.name: ("True", []) for item in config.declarations}
    audit[config.declarations[0].name] = (UNICODE_EXPLICIT_ARGUMENT_LITERAL, [])
    result = verify.VerificationResult(
        config=config,
        module_order=list(__import__("pack_common").BUILD_ORDER),
        audit=audit,
        controls={name: {"status": "PASS", "diagnostic_class": "lean-4.19-type-mismatch",
                         "normalized_sha256": value}
                  for name, value in verify.CONTROL_DIGESTS.items()},
        build={"status": "PASS", "lean": "@lean", "mathlib": "@mathlib",
               "manifest": "@mathlib/lake-manifest.json", "objects": objects,
               "direct_dependencies": {"@mathlib/Mathlib/Tactic.olean": "2" * 64,
                                       "@lean/Init.olean": "4" * 64},
               "dependency_evidence_scope": "lean-direct-import-objects-only",
               "external_cache_boundary": "pinned-checkouts-with-prebuilt-objects-reused",
               "dependency_revisions": verify.DEPENDENCY_PINS,
               "external_caches_reused": True,
               "compiler": {"sha256": "3" * 64, "bytes": 1},
               "mathlib_manifest": {"sha256": verify.MATHLIB_MANIFEST_SHA256, "bytes": 1}},
    )
    issued = root / "issued-verification"
    verify.emit_certificates(result, issued, build)
    issued.rename(package / "verification")
    return package, config.policy


def rewrite_release_certificate(package, name, mutate):
    """Rewrite one synthetic certificate and preserve its outer hash edge."""
    import verify
    certificates = package / "verification" / "certificates"
    target = certificates / name
    document = json.loads(target.read_text())
    mutate(document)
    target.write_bytes(verify._canonical(document))
    if name != "REPRODUCIBILITY_CERTIFICATE.json":
        reproducibility_path = certificates / "REPRODUCIBILITY_CERTIFICATE.json"
        reproducibility = json.loads(reproducibility_path.read_text())
        reproducibility["certificate_hashes"][name] = digest(target)
        reproducibility_path.write_bytes(verify._canonical(reproducibility))


class ReleasePackagerTests(unittest.TestCase):
    def test_unicode_literal_round_trips_through_certificate_and_archive(self):
        from package_release import package_release
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, policy = certified_release_fixture(root)
            certificate_path = package / "verification" / "certificates" / "DECLARATION_CERTIFICATE.json"
            certificate = json.loads(certificate_path.read_text(encoding="ascii"))
            self.assertIn(UNICODE_EXPLICIT_ARGUMENT_LITERAL, certificate["literal_types"].values())
            self.assertIn((chr(92) + "u2200").encode("ascii"), certificate_path.read_bytes())
            output = root / "release.zip"
            package_release(package, output, policy)
            with zipfile.ZipFile(output) as archive:
                archived = json.loads(archive.read(
                    "verification/certificates/DECLARATION_CERTIFICATE.json"))
            self.assertIn(UNICODE_EXPLICIT_ARGUMENT_LITERAL, archived["literal_types"].values())

    def test_packages_exact_43_members_with_acyclic_checksums(self):
        from package_release import package_release
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, policy = certified_release_fixture(root)
            output = root / "release.zip"
            package_release(package, output, policy)
            self.assertTrue(output.is_file())
            with zipfile.ZipFile(output) as archive:
                names = archive.namelist()
                self.assertEqual(43, len(names))
                self.assertEqual(sorted(names), names)
                self.assertEqual(43, len(set(name.casefold() for name in names)))
                self.assertTrue(all(not info.is_dir() and info.compress_type == zipfile.ZIP_STORED
                                    and info.date_time == (1980, 1, 1, 0, 0, 0)
                                    and info.create_system == 3 and not info.extra and not info.comment
                                    and (info.external_attr >> 16) & 0o777 == 0o644
                                    for info in archive.infolist()))
                self.assertIn("MANIFEST.json", names)
                self.assertIn("SHA256SUMS", names)
                manifest = json.loads(archive.read("MANIFEST.json"))
                self.assertEqual(41, len(manifest["members"]))
                checksum_rows = archive.read("SHA256SUMS").decode("ascii").splitlines()
                self.assertEqual(42, len(checksum_rows))
                self.assertNotIn("SHA256SUMS", {row.split("  ", 1)[1] for row in checksum_rows})
                for row in checksum_rows:
                    expected, name = row.split("  ", 1)
                    self.assertEqual(expected, hashlib.sha256(archive.read(name)).hexdigest())

    def test_archive_bytes_are_deterministic_across_absolute_roots(self):
        from package_release import package_release
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            first, first_policy = certified_release_fixture(root / "a")
            second, second_policy = certified_release_fixture(root / "different-location")
            first_zip, second_zip = root / "first.zip", root / "second.zip"
            package_release(first, first_zip, first_policy)
            package_release(second, second_zip, second_policy)
            self.assertEqual(first_zip.read_bytes(), second_zip.read_bytes())
            repeated = root / "repeated.zip"
            package_release(first, repeated, first_policy)
            self.assertEqual(first_zip.read_bytes(), repeated.read_bytes())

    def test_requires_all_certificates_to_be_canonical_pass_records(self):
        from package_release import PackagingError, package_release
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, policy = certified_release_fixture(root)
            certificate = package / "verification" / "certificates" / "BUILD_CERTIFICATE.json"
            document = json.loads(certificate.read_text())
            document["status"] = "FAIL"
            certificate.write_text(json.dumps(document, sort_keys=True, separators=(",", ":")) + "\n",
                                   encoding="ascii")
            with self.assertRaisesRegex(PackagingError, "certificate status"):
                package_release(package, root / "release.zip", policy)
            self.assertFalse((root / "release.zip").exists())
            self.assertFalse((package / "MANIFEST.json").exists())

    def test_rejects_extra_missing_symlink_and_special_tree_members(self):
        from package_release import PackagingError, package_release
        mutations = (
            lambda package: (package / "README.md").unlink(),
            lambda package: (package / "unexpected.log").write_text("stale\n", encoding="utf-8"),
            lambda package: (package / "alias").symlink_to(package / "README.md"),
            lambda package: os.mkfifo(package / "named-pipe"),
        )
        for index, mutate in enumerate(mutations):
            with self.subTest(index=index), tempfile.TemporaryDirectory() as raw:
                root = Path(raw)
                package, policy = certified_release_fixture(root)
                mutate(package)
                with self.assertRaises(PackagingError):
                    package_release(package, root / "release.zip", policy)
                self.assertFalse((root / "release.zip").exists())

    def test_rejects_object_hash_drift_and_existing_output(self):
        from package_release import PackagingError, package_release
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, policy = certified_release_fixture(root)
            target = next((package / "verification" / "build").rglob("*.olean"))
            target.write_bytes(target.read_bytes() + b"changed")
            with self.assertRaisesRegex(PackagingError, "artifact binding"):
                package_release(package, root / "release.zip", policy)
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, policy = certified_release_fixture(root)
            output = root / "release.zip"
            output.write_bytes(b"keep")
            with self.assertRaisesRegex(PackagingError, "output must be fresh"):
                package_release(package, output, policy)
            self.assertEqual(b"keep", output.read_bytes())

    def test_rejects_policy_findings_in_rebound_compiled_objects(self):
        from package_release import PackagingError, package_release
        import verify
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, policy = certified_release_fixture(root)
            target = next((package / "verification" / "build").rglob("*.olean"))
            target.write_bytes(target.read_bytes() + b"__policy_probe__")
            logical = "@run/build/" + target.relative_to(package / "verification" / "build").as_posix()
            rebound = digest(target)
            certificate_root = package / "verification" / "certificates"
            build_doc = json.loads((certificate_root / "BUILD_CERTIFICATE.json").read_text())
            build_doc["objects"][logical] = rebound
            (certificate_root / "BUILD_CERTIFICATE.json").write_bytes(verify._canonical(build_doc))
            privacy_doc = json.loads((certificate_root / "PRIVACY_CERTIFICATE.json").read_text())
            next(row for row in privacy_doc["retained_members"] if row["path"] == logical)["sha256"] = rebound
            (certificate_root / "PRIVACY_CERTIFICATE.json").write_bytes(verify._canonical(privacy_doc))
            reproducibility = json.loads((certificate_root / "REPRODUCIBILITY_CERTIFICATE.json").read_text())
            for name in ("BUILD_CERTIFICATE.json", "PRIVACY_CERTIFICATE.json"):
                reproducibility["certificate_hashes"][name] = digest(certificate_root / name)
            (certificate_root / "REPRODUCIBILITY_CERTIFICATE.json").write_bytes(verify._canonical(reproducibility))
            with self.assertRaisesRegex(PackagingError, "privacy gate"):
                package_release(package, root / "release.zip", policy)

    def test_rejects_whitespace_prefixed_path_shaped_literal_types(self):
        from package_release import PackagingError, package_release
        for whitespace in (" ", "\t", "\n"):
            with self.subTest(whitespace=repr(whitespace)), tempfile.TemporaryDirectory() as raw:
                root = Path(raw)
                package, policy = certified_release_fixture(root)

                def insert_path_shaped_literal(document):
                    name = next(iter(document["literal_types"]))
                    document["literal_types"][name] = whitespace + "@unknown/hidden"

                rewrite_release_certificate(package, "DECLARATION_CERTIFICATE.json",
                                            insert_path_shaped_literal)
                with self.assertRaisesRegex(PackagingError, "certificate path gate"):
                    package_release(package, root / "release.zip", policy)

    def test_rejects_nonmatching_existing_manifest_pair(self):
        from package_release import PackagingError, package_release
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, policy = certified_release_fixture(root)
            (package / "MANIFEST.json").write_text("{}\n", encoding="ascii")
            (package / "SHA256SUMS").write_text("", encoding="ascii")
            with self.assertRaisesRegex(PackagingError, "release metadata"):
                package_release(package, root / "release.zip", policy)

    def test_rejects_one_sided_metadata_and_output_inside_project(self):
        from package_release import PackagingError, package_release
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, policy = certified_release_fixture(root)
            (package / "MANIFEST.json").write_text("{}\n", encoding="ascii")
            with self.assertRaisesRegex(PackagingError, "complete pair"):
                package_release(package, root / "release.zip", policy)
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, policy = certified_release_fixture(root)
            with self.assertRaisesRegex(PackagingError, "outside the project"):
                package_release(package, package / "inside.zip", policy)
            self.assertFalse((package / "inside.zip").exists())
            self.assertFalse((package / "MANIFEST.json").exists())

    def test_uncertified_tree_is_not_packaged(self):
        from package_release import PackagingError, package_release
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, config = VerifierTests().load(root)
            with self.assertRaisesRegex(PackagingError, "exact allowlist"):
                package_release(package, root / "release.zip", config.policy)
            self.assertFalse((root / "release.zip").exists())
            self.assertFalse((package / "MANIFEST.json").exists())

    def test_publish_failure_removes_sidecars_and_temporary_archive(self):
        import package_release as release
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, policy = certified_release_fixture(root)
            output = root / "release.zip"
            with mock.patch.object(release.os, "link", side_effect=OSError("injected publish failure")):
                with self.assertRaisesRegex(release.PackagingError, "publish release archive"):
                    release.package_release(package, output, policy)
            self.assertFalse(output.exists())
            self.assertFalse((package / "MANIFEST.json").exists())
            self.assertFalse((package / "SHA256SUMS").exists())
            self.assertEqual([], list(root.glob(".arithmetic-clock-release-*.tmp")))

    def test_rejects_type_coercive_and_extra_certificate_values(self):
        from package_release import PackagingError, package_release
        mutations = (
            ("PRIVACY_CERTIFICATE.json", lambda document: document.update(finding_count=False)),
            ("SOURCE_CERTIFICATE.json",
             lambda document: document["inputs"][0].update(bytes=float(document["inputs"][0]["bytes"]))),
            ("AXIOM_CERTIFICATE.json",
             lambda document: document["transitive_axioms"].update({"ArithmeticClock.extra": []})),
            ("DECLARATION_CERTIFICATE.json",
             lambda document: document["type_axiom_artifact"].update(
                 bytes=float(document["type_axiom_artifact"]["bytes"]))),
            ("PRIVACY_CERTIFICATE.json",
             lambda document: document["retained_members"][-1].update(
                 bytes=float(document["retained_members"][-1]["bytes"]))),
        )
        for index, (name, mutate) in enumerate(mutations):
            with self.subTest(index=index), tempfile.TemporaryDirectory() as raw:
                root = Path(raw)
                package, policy = certified_release_fixture(root)
                rewrite_release_certificate(package, name, mutate)
                with self.assertRaises(PackagingError):
                    package_release(package, root / "release.zip", policy)

    def test_sidecar_write_failure_removes_the_partial_file(self):
        import package_release as release
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, policy = certified_release_fixture(root)
            real_fsync = release.os.fsync
            calls = 0

            def fail_sidecar_fsync(descriptor):
                nonlocal calls
                calls += 1
                if calls == 2:
                    raise OSError("injected sidecar failure")
                return real_fsync(descriptor)

            with mock.patch.object(release.os, "fsync", side_effect=fail_sidecar_fsync):
                with self.assertRaisesRegex(release.PackagingError, "install release metadata"):
                    release.package_release(package, root / "release.zip", policy)
            self.assertFalse((package / "MANIFEST.json").exists())
            self.assertFalse((package / "SHA256SUMS").exists())
            self.assertFalse((root / "release.zip").exists())

    def test_interrupt_during_sidecar_write_removes_the_partial_file(self):
        import package_release as release
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, policy = certified_release_fixture(root)
            real_fsync = release.os.fsync
            calls = 0

            def interrupt_sidecar_fsync(descriptor):
                nonlocal calls
                calls += 1
                if calls == 2:
                    raise KeyboardInterrupt()
                return real_fsync(descriptor)

            with mock.patch.object(release.os, "fsync", side_effect=interrupt_sidecar_fsync):
                with self.assertRaises(KeyboardInterrupt):
                    release.package_release(package, root / "release.zip", policy)
            self.assertFalse((package / "MANIFEST.json").exists())
            self.assertFalse((package / "SHA256SUMS").exists())
            self.assertFalse((root / "release.zip").exists())
            self.assertEqual([], list(root.glob(".arithmetic-clock-release-*.tmp")))

    def test_rejects_duplicate_and_noncanonical_axiom_lists(self):
        from package_release import PackagingError, package_release
        samples = (
            ["propext", "propext"],
            ["propext", "Classical.choice"],
        )
        for axioms in samples:
            with self.subTest(axioms=axioms), tempfile.TemporaryDirectory() as raw:
                root = Path(raw)
                package, policy = certified_release_fixture(root)

                def mutate(document):
                    name = sorted(document["transitive_axioms"])[0]
                    document["transitive_axioms"][name] = axioms

                rewrite_release_certificate(package, "AXIOM_CERTIFICATE.json", mutate)
                with self.assertRaisesRegex(PackagingError, "axiom certificate"):
                    package_release(package, root / "release.zip", policy)

    def test_package_release_cli_help_and_failure_are_clean(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            source = Path(__file__).resolve().parents[1]
            package = root / "project"
            shutil.copytree(
                source,
                package,
                ignore=shutil.ignore_patterns("__pycache__", "*.pyc"),
            )
            policy = root / "privacy-policy.json"
            blocked = [
                "RH" + "Cayley",
                "RH" + "Bridge",
                "Rie" + "mann",
                "rie" + "mann",
                "tfs." + "cayley",
                "rh-" + "lean-" + "bridge",
            ]
            policy.write_text(
                json.dumps({"schema_version": 1, "blocked": blocked}),
                encoding="ascii",
            )
            script = package / "tools" / "package_release.py"
            environment = dict(os.environ)
            environment.pop("PYTHONDONTWRITEBYTECODE", None)
            help_process = subprocess.run(
                [sys.executable, str(script), "--help"],
                cwd=package,
                env=environment,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=30,
                check=False,
            )
            self.assertEqual(0, help_process.returncode, help_process.stderr)
            output = root / "release.zip"
            failure = subprocess.run(
                [sys.executable, str(script), "--project", str(package),
                 "--privacy-policy", str(policy), "--output", str(output)],
                cwd=root,
                env=environment,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=30,
                check=False,
            )
            self.assertEqual(1, failure.returncode)
            self.assertIn("error:", failure.stderr)
            self.assertNotIn("Traceback", failure.stderr)
            self.assertFalse(output.exists())
            self.assertFalse((package / "MANIFEST.json").exists())
            self.assertFalse((package / "SHA256SUMS").exists())
            self.assertEqual([], list(package.rglob("*.pyc")))
            self.assertEqual([], list(package.rglob("__pycache__")))

    def test_package_release_cli_success_publishes_once(self):
        import package_release as release
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, policy = certified_release_fixture(root)
            output = root / "release.zip"
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                result = release.main([
                    "--project", str(package),
                    "--privacy-policy", str(policy),
                    "--output", str(output),
                ])
            self.assertEqual(0, result)
            self.assertTrue(output.is_file())
            self.assertEqual("created release.zip\n", stdout.getvalue())

    def test_sidecar_creation_race_preserves_the_foreign_file(self):
        import package_release as release
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, policy = certified_release_fixture(root)
            target = package / "MANIFEST.json"
            real_open = release.os.open

            def raced_open(path, flags, mode=0o777):
                if Path(path) == target:
                    target.write_bytes(b"foreign\n")
                    raise FileExistsError(errno.EEXIST, "injected creation race")
                return real_open(path, flags, mode)

            with mock.patch.object(release.os, "open", side_effect=raced_open):
                with self.assertRaisesRegex(release.PackagingError, "install release metadata"):
                    release.package_release(package, root / "release.zip", policy)
            self.assertEqual(b"foreign\n", target.read_bytes())
            self.assertFalse((package / "SHA256SUMS").exists())
            self.assertFalse((root / "release.zip").exists())

    def test_sidecar_close_error_does_not_mask_keyboard_interrupt(self):
        import package_release as release
        with tempfile.TemporaryDirectory() as raw:
            target = Path(raw) / "sidecar"
            real_close = release.os.close

            class Python310Interrupt(KeyboardInterrupt):
                add_note = None

            interrupt = Python310Interrupt()
            caught = None

            class MaskingStream:
                def __enter__(self):
                    return self

                def __exit__(self, *_):
                    raise OSError("injected close failure")

                def write(self, _):
                    raise interrupt

                def flush(self):
                    pass

                def fileno(self):
                    return 0

            def close_then_fail(descriptor):
                real_close(descriptor)
                raise OSError("injected close failure")

            with mock.patch.object(release.os, "fdopen", return_value=MaskingStream()), \
                    mock.patch.object(release.os, "write", side_effect=interrupt), \
                    mock.patch.object(release.os, "close", side_effect=close_then_fail):
                try:
                    release._exclusive_write(target, b"sidecar\n")
                except Python310Interrupt as raised:
                    self.assertIs(interrupt, raised)
                    caught = raised
                except BaseException as raised:
                    self.fail("descriptor cleanup masked the interrupt with " + repr(raised))
                else:
                    self.fail("expected the interrupt")
            self.assertTrue(any("descriptor cleanup" in note
                                for note in caught.__notes__))
            self.assertFalse(target.exists())

    def test_raw_publication_oserror_is_converted_and_cleaned(self):
        import package_release as release
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, policy = certified_release_fixture(root)
            with mock.patch.object(release.os, "chmod", side_effect=OSError("injected chmod failure")):
                with self.assertRaisesRegex(release.PackagingError, "release publication failed"):
                    release.package_release(package, root / "release.zip", policy)
            self.assertFalse((package / "MANIFEST.json").exists())
            self.assertFalse((package / "SHA256SUMS").exists())
            self.assertFalse((root / "release.zip").exists())
            self.assertEqual([], list(root.glob(".arithmetic-clock-release-*.tmp")))

    def test_cleanup_error_preserves_interrupt_and_attempts_all_sidecars(self):
        import package_release as release
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, policy = certified_release_fixture(root)
            real_unlink = Path.unlink
            attempted = []

            class Python310Interrupt(KeyboardInterrupt):
                add_note = None

            interrupt = Python310Interrupt()
            caught = None

            def fail_selected_cleanup(path, *args, **kwargs):
                attempted.append(path.name)
                if path.name.startswith(".arithmetic-clock-release-") or \
                        path.name == "MANIFEST.json":
                    raise OSError("injected temporary cleanup failure")
                return real_unlink(path, *args, **kwargs)

            with mock.patch.object(release.os, "link", side_effect=interrupt), \
                    mock.patch.object(Path, "unlink", autospec=True,
                                      side_effect=fail_selected_cleanup):
                try:
                    release.package_release(package, root / "release.zip", policy)
                except Python310Interrupt as raised:
                    self.assertIs(interrupt, raised)
                    caught = raised
                except BaseException as raised:
                    self.fail("release cleanup masked the interrupt with " + repr(raised))
                else:
                    self.fail("expected the interrupt")
            self.assertTrue(any("cleanup" in note for note in caught.__notes__))
            self.assertTrue((package / "MANIFEST.json").exists())
            self.assertFalse((package / "SHA256SUMS").exists())
            self.assertFalse((root / "release.zip").exists())
            self.assertIn("MANIFEST.json", attempted)
            self.assertIn("SHA256SUMS", attempted)

    def test_interrupt_after_link_rolls_back_the_owned_output(self):
        import package_release as release
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, policy = certified_release_fixture(root)
            output = root / "release.zip"
            real_link = release.os.link

            def link_then_interrupt(source, destination):
                real_link(source, destination)
                raise KeyboardInterrupt()

            with mock.patch.object(release.os, "link", side_effect=link_then_interrupt):
                with self.assertRaises(KeyboardInterrupt):
                    release.package_release(package, output, policy)
            self.assertFalse(output.exists())
            self.assertFalse((package / "MANIFEST.json").exists())
            self.assertFalse((package / "SHA256SUMS").exists())
            self.assertEqual([], list(root.glob(".arithmetic-clock-release-*.tmp")))

    def test_output_eexist_race_preserves_the_collision_file(self):
        import package_release as release
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, policy = certified_release_fixture(root)
            output = root / "release.zip"
            real_link = release.os.link

            def foreign_link_then_eexist(source, destination):
                real_link(source, destination)
                raise FileExistsError(errno.EEXIST, "injected output collision")

            with mock.patch.object(release.os, "link", side_effect=foreign_link_then_eexist):
                with self.assertRaisesRegex(release.PackagingError, "output must be fresh"):
                    release.package_release(package, output, policy)
            self.assertTrue(output.is_file())
            self.assertGreater(output.stat().st_size, 0)
            self.assertFalse((package / "MANIFEST.json").exists())
            self.assertFalse((package / "SHA256SUMS").exists())
            self.assertEqual([], list(root.glob(".arithmetic-clock-release-*.tmp")))

    def test_output_oserror_race_preserves_the_collision_file(self):
        import package_release as release
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, policy = certified_release_fixture(root)
            output = root / "release.zip"
            real_link = release.os.link

            def foreign_link_then_oserror(source, destination):
                real_link(source, destination)
                raise PermissionError(errno.EACCES, "injected output collision")

            with mock.patch.object(release.os, "link", side_effect=foreign_link_then_oserror):
                with self.assertRaisesRegex(release.PackagingError,
                                            "could not publish release archive"):
                    release.package_release(package, output, policy)
            self.assertTrue(output.is_file())
            self.assertGreater(output.stat().st_size, 0)
            self.assertFalse((package / "MANIFEST.json").exists())
            self.assertFalse((package / "SHA256SUMS").exists())
            self.assertEqual([], list(root.glob(".arithmetic-clock-release-*.tmp")))

    def test_sidecar_writer_retries_interrupts_and_short_writes(self):
        import package_release as release
        with tempfile.TemporaryDirectory() as raw:
            target = Path(raw) / "sidecar"
            payload = b"exact deterministic sidecar bytes\n"
            real_write = release.os.write
            calls = 0

            def interrupted_short_write(descriptor, data):
                nonlocal calls
                calls += 1
                if calls == 1:
                    raise InterruptedError()
                return real_write(descriptor, data[:3])

            with mock.patch.object(release.os, "write", side_effect=interrupted_short_write):
                release._exclusive_write(target, payload)
            self.assertEqual(payload, target.read_bytes())
            self.assertGreater(calls, 2)


if __name__ == "__main__":
    unittest.main(verbosity=2)
