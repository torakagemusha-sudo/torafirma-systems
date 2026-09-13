"""Small, fail-closed helpers for the standalone arithmetic-clock verifier."""
from __future__ import annotations

import hashlib
import re
from pathlib import Path, PurePosixPath


LEAN_VERSION = "4.19.0"
LEAN_COMMIT = "6caaee842e94"
MATHLIB_REVISION = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
ROOT_NAMESPACE = "ArithmeticClock"
MODULES = (
    "ArithmeticClock.CyclicCharacters", "ArithmeticClock.DenseCarrier",
    "ArithmeticClock.CyclicTwirl", "ArithmeticClock.DenseTwirl",
    "ArithmeticClock.DivisorGram", "ArithmeticClock.RealClock60",
    "ArithmeticClock.DivisorGram60", "ArithmeticClock.ContinuousReturn60",
    "ArithmeticClock.IntegerClock60",
)
BUILD_ORDER = (
    "ArithmeticClock.DenseCarrier", "ArithmeticClock.DivisorGram", "ArithmeticClock.CyclicCharacters",
    "ArithmeticClock.CyclicTwirl", "ArithmeticClock.DenseTwirl", "ArithmeticClock.RealClock60",
    "ArithmeticClock.DivisorGram60", "ArithmeticClock.ContinuousReturn60", "ArithmeticClock.IntegerClock60",
)
ALLOWED_AXIOMS = frozenset(("propext", "Classical.choice", "Quot.sound"))
EXTERNAL_ROOTS = frozenset(("Mathlib", "Init", "Lean", "Std", "Batteries", "Aesop", "Qq"))
EXTERNAL_MODULES = frozenset((
    "Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar",
    "Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic", "Mathlib.Data.Matrix.Block",
    "Mathlib.Data.Matrix.ConjTranspose", "Mathlib.Data.Matrix.Notation", "Mathlib.Data.Real.Sqrt",
    "Mathlib.Data.Real.StarOrdered", "Mathlib.LinearAlgebra.Matrix.Block",
    "Mathlib.LinearAlgebra.Matrix.PosDef", "Mathlib.NumberTheory.ArithmeticFunction",
    "Mathlib.NumberTheory.Divisors", "Mathlib.Tactic",
))
MODULE_RE = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*\Z")
UNSAFE_RE = re.compile(r"\b(?:sorry|admit|axiom|native_decide|unsafe|run_cmd|run_elab)\b|#\s*(?:eval|reduce)\b")
URI_AUTHORITY_RE = re.compile(r"(?<![A-Za-z0-9_+.\-])([A-Za-z][A-Za-z0-9+.-]*):" + chr(47) * 2,
                              re.IGNORECASE)
OPAQUE_HOST_URI_RE = re.compile(r"(?<![A-Za-z0-9_+.\-])(?:fi" + "le|da" + "ta|ur" +
                                r"n):(?=[^\s\"'=])", re.IGNORECASE)
HTTP_URL_RE = re.compile(r"https?:" + chr(47) * 2 + r"[^\s\"'<>}\]),;]+", re.IGNORECASE)
COMMON_POSIX_ROOTS = frozenset(("bin", "boot", "build", "dev", "etc", "home", "lib", "lib64", "mnt",
                                "nix", "opt", "private", "proc", "project", "root", "run", "sbin", "srv",
                                "sys", "tmp", "usr", "var", "workspace", "Users"))


def add_exception_note(error: BaseException, note: str) -> None:
    """Attach cleanup context without requiring BaseException.add_note."""
    try:
        method = getattr(error, "add_note", None)
        if callable(method):
            method(note)
            return
        notes = getattr(error, "__notes__", None)
        if not isinstance(notes, list):
            notes = []
            setattr(error, "__notes__", notes)
        notes.append(note)
    except BaseException:
        pass


def has_absolute_host_path(text: str) -> bool:
    """Classify inspectable plaintext, including strings and comment bodies."""
    normalized = text.translate({8726: chr(92), 65340: chr(92)})
    if any(matched.group(1).lower() not in ("http", "https")
           for matched in URI_AUTHORITY_RE.finditer(normalized)):
        return True
    if OPAQUE_HOST_URI_RE.search(normalized) or _has_rooted_windows_path(normalized):
        return True
    without_remote = list(normalized)
    for matched in HTTP_URL_RE.finditer(normalized):
        without_remote[matched.start():matched.end()] = " " * (matched.end() - matched.start())
    return _has_posix_host_path("".join(without_remote))


def _has_rooted_windows_path(text: str) -> bool:
    separator = chr(92)
    if re.search(r"(?<![A-Za-z0-9_])[A-Za-z]:[" + separator * 2 + chr(47) + r"]", text):
        return True
    boundaries = set(" \"'`=([{,:;}") | {chr(9), chr(10), chr(13)}
    stops = boundaries | set(")]<>|+*")

    def raw_regex_escape(at: int) -> bool:
        line_start = text.rfind(chr(10), 0, at) + 1
        inside = False
        for marker in ('r"', "r'", 'rb"', "rb'", 'br"', "br'"):
            start = text.rfind(marker, line_start, at)
            if start < 0:
                continue
            closing = text.find(marker[-1], start + len(marker))
            inside = inside or closing < 0 or closing >= at
        if not inside:
            return False
        cursor, count = at, 0
        regex_escapes = "AbBdDsSwWxXZ.[](){}+*?|^-"
        while cursor + 1 < len(text) and text[cursor] == separator and text[cursor + 1] in regex_escapes:
            count += 1
            cursor += 2
        return count > 0 and (cursor >= len(text) or text[cursor] in "|:()[]{}*+?.^$,")

    for index, value in enumerate(text):
        if value != separator or (index and text[index - 1] not in boundaries):
            continue
        if raw_regex_escape(index):
            continue
        run_end = index
        while run_end < len(text) and text[run_end] == separator:
            run_end += 1
        end = run_end
        while end < len(text) and text[end] not in stops and text[end] != separator:
            end += 1
        component = text[run_end:end]
        if not component:
            continue
        if text.startswith(separator + "frac{", index):
            continue
        if index and text[index - 1] in ("\"", "'") and component[:1] in "abfnrtv":
            escape_end = index
            escape_count = 0
            while escape_end + 1 < len(text) and text[escape_end] == separator and \
                    text[escape_end + 1] in "abfnrtv":
                escape_count += 1
                escape_end += 2
            if escape_count > 1 or (escape_count == 1 and escape_end < len(text) and
                                    text[escape_end] in ("\"", "'")):
                continue
            if len(component) > 1 and not component[1].isalnum():
                continue
        if run_end - index >= 2:
            return True
        if end < len(text) and text[end] == separator:
            return True
        if len(component) == 1:
            if index == 0:
                return True
            continue
        return True
    return False


def _has_posix_host_path(text: str) -> bool:
    separator = chr(47)
    boundary = set("\"'`=([{,:;}")
    for index, value in enumerate(text):
        if value != separator:
            continue
        previous = text[index - 1] if index else ""
        if previous and (previous.isalnum() or previous in "_.$" or previous == chr(92)):
            continue
        end = index + 1
        while end < len(text) and not text[end].isspace() and text[end] not in "\"'<>)]},;":
            end += 1
        token = text[index:end]
        first = token[1:].split(separator, 1)[0]
        if token == separator * 2:
            before, after = text[:index].rstrip(), text[end:].lstrip()
            opening, closing = before.rfind("{"), before.rfind("}")
            if opening > closing and ":" in before[opening:] and re.match(r"[A-Za-z_][A-Za-z0-9_']*", after):
                continue
            return True
        if index == 0 or previous in boundary:
            return True
        if len(token) == 1:
            prefix = text[max(0, index - 32):index]
            tail = text[end:]
            if (not tail or tail[0] in "\r\n\"')]}>,;") and \
                    re.search(r"(?:cwd|directory|path|root)\s*[:=]?\s*$", prefix, re.IGNORECASE):
                return True
            continue
        if separator in token[1:] or first in COMMON_POSIX_ROOTS:
            return True
        if previous.isspace() and len(first) >= 2:
            prefix = text[max(0, index - 48):index]
            if re.search(r"(?:source|file|cwd|directory|path|root|working\s+directory)\s*[:=]?\s*$",
                         prefix, re.IGNORECASE):
                return True
    return False


def has_compiled_host_path(raw: bytes) -> bool:
    """Find high-confidence host paths in opaque compiled-object bytes."""
    visible = bytes(value if 32 <= value <= 126 else 32 for value in raw)
    slash, backslash = bytes((47,)), bytes((92,))
    remote = re.compile(rb"(?<![A-Za-z0-9_+.-])https?:" + re.escape(slash * 2) +
                        rb"[^\s\"'<>}\]),;]+", re.IGNORECASE)
    visible = remote.sub(lambda matched: b" " * len(matched.group(0)), visible)
    non_http_authority = re.compile(rb"(?<![A-Za-z0-9_+.-])[A-Za-z][A-Za-z0-9+.-]*:" +
                                    re.escape(slash * 2), re.IGNORECASE)
    opaque_host = re.compile(rb"(?<![A-Za-z0-9_+.-])(?:fi" + b"le:(?=" + re.escape(slash) +
                             b")|da" + b"ta:|ur" + b"n:)",
                             re.IGNORECASE)
    if non_http_authority.search(visible) is not None or opaque_host.search(visible) is not None:
        return True
    separator_pattern = b"(?:" + re.escape(backslash) + b"|/)"
    drive = re.compile(rb"(?<![A-Za-z0-9_])[A-Za-z]:" + separator_pattern +
                       rb"[A-Za-z0-9_.$-]{1,}" + separator_pattern + rb"[A-Za-z0-9_.$/-]{1,}")
    unc_component = rb"[^" + re.escape(backslash) + re.escape(slash) + rb"\s]{1,64}"
    unc = re.compile(re.escape(backslash * 2) + unc_component + re.escape(backslash) + unc_component)
    component = rb"[A-Za-z0-9_.+@$=-]{1,64}"
    roots = rb"(?:bin|boot|build|dev|etc|home|lib|lib64|mnt|nix|opt|private|proc|project|root|run|sbin|srv|sys|tmp|usr|var|workspace|Users)"
    known_posix = re.compile(rb"(?<![A-Za-z0-9_])" + slash + roots + slash + component)
    generic_posix = re.compile(rb"(?<![A-Za-z0-9_])" + slash + component + slash + component)
    return (drive.search(visible) is not None or unc.search(visible) is not None or
            known_posix.search(visible) is not None or generic_posix.search(visible) is not None)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def uncomment(text: str, mask_strings: bool = True) -> str:
    """Mask nested comments and strings without changing line positions."""
    output: list[str] = []
    index = 0
    depth = 0
    while index < len(text):
        if depth:
            if text.startswith(chr(47) + "-", index):
                depth += 1
                output.extend("  ")
                index += 2
            elif text.startswith("-" + chr(47), index):
                depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif text.startswith(chr(47) + "-", index):
            depth = 1
            output.extend("  ")
            index += 2
        elif text.startswith("--", index):
            end = text.find("\n", index)
            if end < 0:
                output.extend(" " * (len(text) - index))
                break
            output.extend(" " * (end - index))
            output.append("\n")
            index = end + 1
        elif text[index] == '"':
            start = index
            index += 1
            while index < len(text):
                if text[index] == "\\":
                    index += 2
                elif text[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
            else:
                raise ValueError("unterminated Lean string")
            segment = text[start:index]
            output.append("".join("\n" if char == "\n" else " " for char in segment) if mask_strings else segment)
        else:
            output.append(text[index])
            index += 1
    if depth:
        raise ValueError("unterminated nested Lean comment")
    return "".join(output)


def scan_lean(text: str) -> str:
    clean = uncomment(text)
    found = UNSAFE_RE.search(clean)
    if found:
        raise ValueError("unsafe production token: " + found.group(0))
    if "«" in clean or "»" in clean:
        raise ValueError("quoted identifiers require parser review")
    return clean


def parse_imports(text: str) -> list[str]:
    clean = scan_lean(text)
    result: list[str] = []
    for matched in re.finditer(r"^\s*import\s+([^\n]+)$", clean, re.MULTILINE):
        for name in matched.group(1).split():
            if not MODULE_RE.fullmatch(name):
                raise ValueError("unsupported import syntax: " + name)
            if name in result:
                raise ValueError("duplicate import: " + name)
            result.append(name)
    return result


def is_external(module: str) -> bool:
    return module in EXTERNAL_MODULES


def safe_relative(value: str) -> PurePosixPath:
    separator = chr(47)
    if (not isinstance(value, str) or not value or "\\" in value or "\0" in value or value.startswith(separator * 2) or
            ":" + separator * 2 in value or value.startswith("." + separator) or value.endswith(separator) or separator * 2 in value):
        raise ValueError("invalid package path")
    path = PurePosixPath(value)
    if path.is_absolute() or "." in path.parts or ".." in path.parts or any(part.startswith("-") for part in path.parts) or ":" in value:
        raise ValueError("invalid package path")
    return path


def local_source_path(module: str) -> str:
    if module not in MODULES:
        raise ValueError("unallowlisted local module: " + module)
    return PurePosixPath(*module.split(".")).with_suffix(".lean").as_posix()


def topo_sort(graph: dict[str, list[str]], entries: list[str]) -> list[str]:
    result: list[str] = []
    active: set[str] = set()
    done: set[str] = set()

    def visit(node: str) -> None:
        if node not in graph:
            raise ValueError("missing local module: " + node)
        if node in active:
            raise ValueError("local import cycle: " + node)
        if node in done:
            return
        active.add(node)
        for item in graph[node]:
            if item in graph:
                visit(item)
            elif not is_external(item):
                raise ValueError("unlisted local import: " + item)
        active.remove(node)
        done.add(node)
        result.append(node)

    for entry in entries:
        visit(entry)
    return result
