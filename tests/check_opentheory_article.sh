#!/usr/bin/env bash
#
# Checks an OpenTheory article file with Joe Leslie-Hurd's opentheory tool, the reference
# reader of the format (version 6, https://www.gilith.com/opentheory/article.html), so that
# a Gezi test can check a trace, which is an OpenTheory article, with a tool independent of
# Gezi.
#
# Usage: check_opentheory_article.sh ARTICLE
#
# The command it runs:
#
#   opentheory info --inference article:ARTICLE
#
# `info` reads the article, executing each command under the constraints of the format, the
# thm commands' checks of their theorems included, and with `--inference` prints on standard
# output the count of each inference rule the article's proofs use. It prints no term: the
# tool's default output, the theory the article proves with its assumptions and theorems,
# warns "term too large to print" on standard error for the theorems of the articles whose
# terms carry the markers spelled `(λ"$t". M) "$t"`, each applied to its own synthetic label
# (measured 2026-11-19 on successor_zero_type_check.art), a warning about printing, not
# about the article. The prefix `article:` makes the tool read ARTICLE as an article
# whatever the file is named; it needs no package repository. Warnings and errors go to
# standard error. On the two fixtures in opentheory_fixtures/ beside this script, run from
# gezi/tests:
#
#   ./check_opentheory_article.sh opentheory_fixtures/accepted_choice_commutativity_instance.art
#   exits with status 0 and prints on standard output
#     Inference rules:
#     axiom ... 1
#     subst ... 1
#
#   ./check_opentheory_article.sh opentheory_fixtures/rejected_wrong_conclusion.art
#   exits with status 1 and prints on standard error, after an empty line,
#     FATAL ERROR: opentheory failed:
#     error in file "opentheory_fixtures/rejected_wrong_conclusion.art" around line 167:
#     varTerm
#     appTerm
#     thm
#     while executing thm command:
#     terms not alpha-equivalent
#
# Exit status: 0 when the tool accepts the article, that is, its theorems derive from its
# assumptions; 1 when the tool rejects it; 2 on a usage error, a missing ARTICLE included
# (the tool itself exits with 1 on a file it cannot open); 127 when opentheory is not on
# the PATH. A warning does not fail the check: the tool prints it on standard error and
# exits with 0, as it does for objects left in the dictionary at the end of the article,
# and for a command of version 6 (sym, trans, ...) in an article that does not begin with
# `6` and `version`, which the tool reads as version 5.
#
# The tool is the flake output opentheory (gezi/modules/opentheory.nix,
# `nix build .#opentheory -L`, version 1.4, release 20230321) and is on the dev shell's
# PATH: `direnv exec . gezi/tests/check_opentheory_article.sh ARTICLE`.

set -o errexit
set -o nounset
set -o pipefail

if [ "$#" -ne 1 ]; then
    echo "usage: $0 ARTICLE" >&2
    exit 2
fi
article=$1
if [ ! -f "$article" ]; then
    echo "$0: no such article file: $article" >&2
    exit 2
fi

exec opentheory info --inference "article:$article"
