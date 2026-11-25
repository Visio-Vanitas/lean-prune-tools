"""Relaxation policies for closeD.

closeD finds every *soft* edge that blocks deleting a candidate set B and asks the policy what to do.
An edge is described by an Edge record; the policy returns one of:
    KEEP   - keep the providing module(s) (remove them from B)
    RELAX  - delete anyway and repair the source (e.g. strip the dead token from an `open` line)
    IGNORE - edge does not actually block (nothing to do)

Hard edges (a kept declaration uses a declaration in B) always KEEP.

Select a policy via --policy or RELAX_POLICY=<name> (default: conservative).
"""
from __future__ import annotations

import os
from dataclasses import dataclass, field
from typing import Callable

KEEP, RELAX, IGNORE = "keep", "relax", "ignore"


@dataclass
class Edge:
    kind: str  # 'open-namespace' | 'zero-const-import' | 'text-ref'
    user: str
    token: str = ""
    target: str = ""
    providers_in_B: set[str] = field(default_factory=set)
    visible_before: bool = True
    visible_after: bool = False
    external: bool = False
    inert: bool = False
    failed_before: bool = False


POLICIES: dict[str, Callable[[Edge], str]] = {}


def policy(fn: Callable[[Edge], str]) -> Callable[[Edge], str]:
    POLICIES[fn.__name__] = fn
    return fn


@policy
def conservative(e: Edge) -> str:
    if e.kind == "open-namespace":
        if e.external or e.visible_after:
            return IGNORE
        if e.visible_before and not e.failed_before:
            return RELAX
        return KEEP
    if e.kind == "zero-const-import":
        return RELAX if e.inert else KEEP
    return KEEP


@policy
def aggressive(e: Edge) -> str:
    """Relax by default; never touches external (Mathlib/core) namespaces."""
    if e.kind == "open-namespace":
        if e.external or e.visible_after:
            return IGNORE
        return KEEP if e.failed_before else RELAX
    if e.kind == "zero-const-import":
        return KEEP if e.failed_before else RELAX
    return KEEP


def get(name: str | None = None) -> tuple[str, Callable[[Edge], str]]:
    chosen = name or os.environ.get("RELAX_POLICY") or ("aggressive" if os.environ.get("AGGR") else "conservative")
    if chosen not in POLICIES:
        raise ValueError(f"Unknown relax policy {chosen!r}; expected one of {sorted(POLICIES)}")
    return chosen, POLICIES[chosen]
