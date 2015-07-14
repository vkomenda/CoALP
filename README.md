# CoALP

:copyright: 2014-2015: CoALP project, University of Dundee

License: LGPL v3


## Synopsis


Haskell implementation of coalgebraic logic programming. Experimental,
development version.


## Installation


### Standard installation using `cabal`

Run from the project directory:

> `cabal install`


### Installation with optional tests

Run from the project directory:

> `cabal install --enable-tests`

Then you can run the test suite `CoALP-tests` from its install location.


### External requirements

`Graphwiz` is required for saving derivations, in particular the `dot` tool.

`eog` is currently hardcoded as the viewer for saved files. These are however
standard PNG files compatible with a generic graphics viewer.


## Usage instructions


Please refer to the help in `CoALPi -h`.

There are two modes of operation of CoALPi: interactive (default) and
non-interactive (switched on by the option `-n`).

The non-interactive mode can be used for scripting purposes as it accepts
programs and goals through a standard Unix pipe like this:

> `cat programs/typeinference/typeinf.logic | CoALPi -n`

The interactive mode is designed for iterating through derivations. The
suggested interactive command workflow is:

 - `program`, `goal`, `search` (possibly multiple times) or `check`; then `save`
   and `view` followed by `exit`.

Interactive mode also accepts loading from files as follows:

> `CoALPi -l programs/typeinference/typeinf.logic`
