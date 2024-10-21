FROM rocq/rocq-prover:9.1.1-native-ocaml-4.14.2-flambda 
RUN eval $(opam env "--switch=${COMPILER}" --set-switch)
RUN opam update -y
RUN opam install -y rocq-core.9.1.1 rocq-stdlib.9.0.0 rocq-elpi rocq-mathcomp-character.2.5.0 rocq-mathcomp-analysis.1.16.0 vsrocq-language-server coq-mathcomp-algebra-tactics coq-mathcomp-zify
