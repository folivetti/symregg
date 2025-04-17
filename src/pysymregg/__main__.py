import sys
from typing import NoReturn
import pysymregg


def main() -> NoReturn:
    sys.exit(pysymregg.main(sys.argv))


if __name__ == "__main__":
    main()
