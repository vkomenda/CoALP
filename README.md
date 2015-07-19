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


### CoALPi commands, in a bit more details

`program` lets you input the list of clauses. You may have already loaded it
from the command line using `-l`.

`goal` lets you input the list of goals. You need to input only one goal of the
kind

> `:- p1(t1_1, ..., t1_n), ..., pm(tm_1, ..., tm_k).`

Multiple goals are possible, but this functionality isn't finished yet.

Once you have both a program and a goal loaded, you can start a derivation by
`search`. When CoALPi halts with a list of successful trees, you can continue
the same derivation by issuing the `search` command again.

`check` is for building an observation (tier 3 guardedness check) which is a
special kind of derivation. It's supposed to output unguarded loops if there are
any.

Both the derivation and the observation can be saved to files using the command
`save`. In the target directory you will find PNG files that you can view in a
viewer or in a web browser. The numbered files contain all the trees in the
derivation. There is also a file `overview.gv.png` which contains terms in goal
nodes of each of those trees, and transitions between the trees.

The overview file of an observation is slightly more informative when describing
transitions, which can be used for debugging.
