import sys

from typing import List

if sys.version_info < (3, 8):
    from typing_extensions import Protocol
else:
    from typing import Protocol


class Session(Protocol):
    def version(self) -> str: ...
    def main(self, args: List[str] = []) -> int: ...
    def pysymregg_run(self, dataset: str, gen: int, alg: str, maxSize: int, nonterminals: str, loss: str, optIter: int, optRepeat: int, nParams: int, split: int, dumpTo: str, loadFrom: str) -> str: ...
