"""Bounded public lookups and provider-specific audit records."""

from __future__ import annotations

import argparse
import ipaddress
import json
import socket
import time
from typing import Any
from urllib.error import HTTPError, URLError
from urllib.parse import quote, urlencode, urlparse
from urllib.request import HTTPRedirectHandler, Request, build_opener
from xml.etree import ElementTree

from .metadata import (
    arxiv_api_url,
    arxiv_metadata,
    arxiv_rights,
    crossref_external,
    html_external,
)
from .comparisons import (
    classify,
    metadata_comparisons,
    unavailable_comparisons,
)
from .schema import (
    RIGHTS_UNAVAILABLE,
    extract_arxiv_id,
    extract_doi,
    input_fingerprint,
    utc_now,
)


class HostRateLimiter:
    """Sequential, host-aware pauses. This is intentionally conservative."""

    def __init__(self, crossref_delay: float, arxiv_delay: float, web_delay: float) -> None:
        self.crossref_delay = crossref_delay
        self.arxiv_delay = arxiv_delay
        self.web_delay = web_delay
        self.last_request: dict[str, float] = {}

    def delay(self, url: str) -> float:
        host = urlparse(url).netloc.casefold()
        if host == "api.crossref.org":
            return self.crossref_delay
        if host.endswith("arxiv.org"):
            return self.arxiv_delay
        return self.web_delay

    def wait(self, url: str) -> None:
        host = urlparse(url).netloc.casefold()
        elapsed = time.monotonic() - self.last_request.get(host, float("-inf"))
        remaining = self.delay(url) - elapsed
        if remaining > 0:
            time.sleep(remaining)
        self.last_request[host] = time.monotonic()


def retry_after_seconds(value: str | None) -> float:
    """Honor a numeric Retry-After header without letting it sleep indefinitely."""
    try:
        return min(max(float(value or "0"), 0.0), 60.0)
    except ValueError:
        return 0.0


class UnsafeURLError(ValueError):
    """Raised when a URL targets a non-public, non-HTTP, or non-global destination."""


def _check_ip_public(ip: ipaddress.IPv4Address | ipaddress.IPv6Address) -> None:
    if ip.is_loopback:
        raise UnsafeURLError(f"loopback address rejected ({ip})")
    if ip.is_private:
        raise UnsafeURLError(f"private address rejected ({ip})")
    if ip.is_link_local:
        raise UnsafeURLError(f"link-local address rejected ({ip})")
    if ip.is_multicast:
        raise UnsafeURLError(f"multicast address rejected ({ip})")
    if ip.is_reserved:
        raise UnsafeURLError(f"reserved address rejected ({ip})")
    if ip.is_unspecified:
        raise UnsafeURLError(f"unspecified address rejected ({ip})")
    if not ip.is_global:
        raise UnsafeURLError(f"non-global address rejected ({ip})")


def validate_public_url(url: str) -> None:
    parsed = urlparse(url)
    scheme = parsed.scheme.lower()
    if scheme not in {"http", "https"}:
        raise UnsafeURLError(f"unsupported scheme {parsed.scheme!r}")
    if parsed.username is not None or parsed.password is not None:
        raise UnsafeURLError("userinfo is not permitted in URL")
    hostname = parsed.hostname
    if not hostname:
        raise UnsafeURLError("missing host in URL")

    hostname_clean = hostname.rstrip(".").lower()
    if hostname_clean == "localhost" or hostname_clean.endswith(".localhost"):
        raise UnsafeURLError(f"localhost destination rejected ({hostname})")

    try:
        ip = ipaddress.ip_address(hostname_clean)
        _check_ip_public(ip)
        return
    except ValueError:
        pass

    try:
        addrinfo = socket.getaddrinfo(hostname_clean, None)
    except socket.gaierror as err:
        raise URLError(f"could not resolve host {hostname_clean}: {err}") from err

    if not addrinfo:
        raise UnsafeURLError(f"no addresses resolved for {hostname_clean}")

    for res in addrinfo:
        ip_str = res[4][0]
        try:
            ip = ipaddress.ip_address(ip_str)
            _check_ip_public(ip)
        except ValueError as err:
            raise UnsafeURLError(f"invalid resolved address {ip_str}: {err}") from err


class SafeRedirectHandler(HTTPRedirectHandler):
    """Ensure HTTP redirect targets remain within public HTTP(S) destinations."""

    def redirect_request(
        self, req: Request, fp: Any, code: int, msg: str, headers: Any, newurl: str
    ) -> Request | None:
        validate_public_url(newurl)
        return super().redirect_request(req, fp, code, msg, headers, newurl)


def fetch(
    url: str,
    limiter: HostRateLimiter,
    user_agent: str,
    timeout: float,
    max_bytes: int,
    retries: int,
) -> tuple[bytes | None, str, str]:
    """Return body, final URL, error; retry only transient public HTTP failures."""
    opener = build_opener(SafeRedirectHandler())
    for attempt in range(retries + 1):
        limiter.wait(url)
        request = Request(
            url,
            headers={
                "Accept": (
                    "application/json, application/atom+xml, application/xml;q=0.95, "
                    "text/html;q=0.9, application/xhtml+xml;q=0.8"
                ),
                "User-Agent": user_agent,
            },
        )
        try:
            validate_public_url(url)
            with opener.open(request, timeout=timeout) as response:
                body = response.read(max_bytes + 1)
                if len(body) > max_bytes:
                    return None, response.geturl(), f"response exceeded {max_bytes} byte limit"
                return body, response.geturl(), ""
        except HTTPError as error:
            message = f"HTTP {error.code}"
            transient = error.code in {429, 500, 502, 503, 504}
            retry_after = retry_after_seconds(error.headers.get("Retry-After"))
        except URLError as error:
            if isinstance(error.reason, UnsafeURLError):
                raise error.reason
            message = f"network error: {error.reason}"
            transient = True
            retry_after = 0.0
        except OSError as error:
            message = f"request error: {error}"
            transient = True
            retry_after = 0.0
        if not transient or attempt == retries:
            return None, url, message
        time.sleep(max(limiter.delay(url), 2**attempt, retry_after))
    raise AssertionError("unreachable")


def crossref_url(doi: str, mailto: str | None) -> str:
    url = f"https://api.crossref.org/v1/works/{quote(doi, safe='')}"
    return f"{url}?{urlencode({'mailto': mailto})}" if mailto else url


def failed_record(
    source: dict[str, Any],
    provider: str,
    lookup_status: str,
    checked_url: str,
    note: str,
) -> dict[str, Any]:
    comparisons = unavailable_comparisons(source, "UNAVAILABLE")
    rights = {
        "outcome": RIGHTS_UNAVAILABLE,
        "details": note,
        "url": checked_url,
    }
    return {
        "input_fingerprint": input_fingerprint(source),
        "provider": provider,
        "lookup_status": lookup_status,
        "checked_url": checked_url,
        "checked_on": utc_now(),
        "metadata": comparisons,
        "rights": rights,
        "related_dois": [],
        "status": classify(lookup_status, comparisons, rights, []),
        "notes": note,
    }


def successful_record(
    source: dict[str, Any],
    provider: str,
    checked_url: str,
    comparison_locator: str,
    external: dict[str, Any],
    notes: str = "",
) -> dict[str, Any]:
    comparisons = metadata_comparisons(source, external, True, comparison_locator)
    rights = external["rights"]
    related_dois = external.get("related_dois", [])
    return {
        "input_fingerprint": input_fingerprint(source),
        "provider": provider,
        "lookup_status": "OK",
        "checked_url": checked_url,
        "checked_on": utc_now(),
        "metadata": comparisons,
        "rights": rights,
        "related_dois": related_dois,
        "status": classify("OK", comparisons, rights, related_dois),
        "notes": notes,
    }


def evaluate_html_source(
    source: dict[str, Any],
    locator: str,
    args: argparse.Namespace,
    limiter: HostRateLimiter,
    note_prefix: str = "",
) -> dict[str, Any]:
    body, final_url, error = fetch(
        locator,
        limiter,
        args.user_agent,
        args.timeout,
        args.max_bytes,
        args.retries,
    )
    if body is None:
        return failed_record(source, "html", "HTTP_ERROR", locator, f"{note_prefix}{error}")
    try:
        external = html_external(body, final_url)
    except (UnicodeError, ValueError) as error:
        return failed_record(
            source,
            "html",
            "PARSE_ERROR",
            final_url,
            f"{note_prefix}Could not parse HTML: {error}",
        )
    return successful_record(
        source, "html", final_url, final_url, external, note_prefix.rstrip()
    )


def evaluate_arxiv_source(
    source: dict[str, Any],
    locator: str,
    arxiv_id: str,
    args: argparse.Namespace,
    limiter: HostRateLimiter,
) -> dict[str, Any]:
    """Use arXiv's structured metadata and its visible per-paper license link."""
    request_url = arxiv_api_url(arxiv_id)
    body, final_url, error = fetch(
        request_url,
        limiter,
        args.user_agent,
        args.timeout,
        args.max_bytes,
        args.retries,
    )
    if body is None:
        return evaluate_html_source(
            source,
            locator,
            args,
            limiter,
            f"arXiv API lookup failed ({error}); checked the source locator instead. ",
        )
    try:
        external, notes = arxiv_metadata(body, arxiv_id)
    except (ElementTree.ParseError, UnicodeError, ValueError) as error:
        return evaluate_html_source(
            source,
            locator,
            args,
            limiter,
            f"Could not parse arXiv API metadata ({error}); checked the source locator instead. ",
        )
    abstract_body, abstract_url, abstract_error = fetch(
        locator,
        limiter,
        args.user_agent,
        args.timeout,
        args.max_bytes,
        args.retries,
    )
    if abstract_body is None:
        external["rights"] = {
            "outcome": RIGHTS_UNAVAILABLE,
            "details": (
                "Could not retrieve the arXiv abstract page for its per-paper license "
                f"link: {abstract_error}"
            ),
            "url": locator,
        }
        notes = " ".join(
            part
            for part in (
                notes,
                "Metadata came from the arXiv API; the abstract page could not be retrieved.",
            )
            if part
        )
    else:
        external["rights"] = arxiv_rights(abstract_body, abstract_url)
    return successful_record(source, "arxiv", final_url, locator, external, notes)


def evaluate_source(
    source: dict[str, Any], args: argparse.Namespace, limiter: HostRateLimiter
) -> dict[str, Any]:
    locator = source.get("locator", "")
    if not locator:
        return failed_record(
            source,
            "none",
            "MISSING_LOCATOR",
            "",
            "No locator is recorded in registry.yaml.",
        )
    arxiv_id = extract_arxiv_id(locator)
    if arxiv_id:
        return evaluate_arxiv_source(source, locator, arxiv_id, args, limiter)
    doi = extract_doi(locator) or extract_doi(source["citation"])
    if doi:
        request_url = crossref_url(doi, args.mailto)
        body, final_url, error = fetch(
            request_url,
            limiter,
            args.user_agent,
            args.timeout,
            args.max_bytes,
            args.retries,
        )
        checked_url = crossref_url(doi, None)
        if body is None:
            if error == "HTTP 404":
                return evaluate_html_source(
                    source,
                    locator,
                    args,
                    limiter,
                    "Crossref returned HTTP 404; checked the source locator instead. ",
                )
            return failed_record(source, "crossref", "HTTP_ERROR", checked_url, error)
        try:
            payload = json.loads(body)
            message = payload["message"]
            if not isinstance(message, dict):
                raise ValueError("Crossref response has no object message")
            external = crossref_external(message)
        except (ValueError, TypeError, KeyError, json.JSONDecodeError) as error:
            return failed_record(
                source,
                "crossref",
                "PARSE_ERROR",
                checked_url,
                f"Could not parse Crossref metadata: {error}",
            )
        return successful_record(source, "crossref", checked_url, locator, external)
    return evaluate_html_source(source, locator, args, limiter)
