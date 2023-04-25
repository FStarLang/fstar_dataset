all: fstar_insights.exe

# Find fstar.exe and the fstar.lib OCaml package
ifeq (,$(FSTAR_HOME))
  _check_fstar := $(shell which fstar.exe)
  ifeq ($(.SHELLSTATUS),0)
    _fstar_home := $(realpath $(dir $(_check_fstar))/..)
    ifeq ($(OS),Windows_NT)
      OCAMLPATH := $(shell cygpath -m $(_fstar_home)/lib);$(OCAMLPATH)
    else
      OCAMLPATH := $(_fstar_home)/lib:$(OCAMLPATH)
    endif
  endif
else
  ifeq ($(OS),Windows_NT)
    OCAMLPATH := $(shell cygpath -m $(FSTAR_HOME)/lib);$(OCAMLPATH)
  else
    OCAMLPATH := $(FSTAR_HOME)/lib:$(OCAMLPATH)
  endif
endif
export OCAMLPATH
_check_fstar_lib_package := $(shell env OCAMLPATH="$(OCAMLPATH)" ocamlfind query fstar.lib)
ifneq ($(.SHELLSTATUS),0)
  $(error "Cannot find fstar.lib in $(OCAMLPATH). Please make sure fstar.exe is properly installed and in your PATH or FSTAR_HOME points to its prefix directory or the F* source repository.")
endif

# Define the Steel root directory. We need to fix it to use the Windows path convention on Windows+Cygwin.
ifeq ($(OS),Windows_NT)
  INSTALL_HOME := $(shell cygpath -m $(CURDIR))
else
  INSTALL_HOME := $(CURDIR)
endif

fstar_insights.exe:
	dune build
	dune install --prefix=$(INSTALL_HOME)
