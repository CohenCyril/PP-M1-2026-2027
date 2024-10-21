# -*- Makefile -*-

# setting variables
COQPROJECT?=_CoqProject
COQMAKEOPTIONS=--no-print-directory

# Main Makefile
include Makefile.common

tutorial.html: tutorial.vo tutorial.glob
	rocqnavi tutorial.v
