#!/usr/bin/env python3
"""Check that publication metadata is the only difference between manuscript bodies."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
INTRO = r'\section{Introduction}'
DECLARATION = re.compile(
    r'\\subsection\{AI-assisted proof development and verification status\}\s*'
    r'\\label\{subsec:ai-declaration\}.*?(?=\\section\{Proofs of Theorems)', re.S)


def verify():
    published = (ROOT.parent / 'SRW_max_local_time.tex').read_text()
    certified = (ROOT / 'source/SRW_max_local_time.tex').read_text()
    body = published[published.index(INTRO):]
    body, count = DECLARATION.subn('', body)
    if count != 1 or body != certified[certified.index(INTRO):]:
        raise ValueError('Publication manuscript differs from the certified mathematical body')
    abstract = re.compile(r'\\begin\{abstract\}(.*?)\\end\{abstract\}', re.S)
    if abstract.search(published).group(1) != abstract.search(certified).group(1):
        raise ValueError('Publication and certified abstracts differ')
    print('PASS: publication and checksum-bound manuscripts have identical mathematical bodies.')


if __name__ == '__main__':
    verify()
