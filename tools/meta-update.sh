#!/usr/bin/env bash

TMP=$(mktemp -d); git clone https://github.com/coq-community/templates.git $TMP
nix-shell -p mustache-go --run $TMP/generate.sh