# Imports
To import another module, use the `import` directive, or the `:import` (or `:i`)
command in the REPL.  The name of the module is specified in _dotted notation_:
a sequence of names separated by dots.  There are two ways to specify an import:
absolute import or relative import.


## Absolute Imports
Absolute imports should be preferred.  The module name is resolved relative
to the root module or the REPL working directory.
For example, if the root module lives in `/myproject/`, the following import:

    import utils.extra

Will expect to find the module `utils.extra` in `/myproject/utils/extra.stx`
(`utils/extra.stx` relative to the base directory).  If `extra.stx` specifies its
own absolute import, for example:

    import common

Then the module `common` is expected to be found at `/myproject/common.stx`
(`common.stx` relative to the base directory).


## Relative Imports
Relative imports should be avoided.  The module name is resolved relative
to the current file.
For example, if the current module lives in `/myproject/`. the following import:

    import .utils.extra

Will expect to find the module `utils.extra` in `/myproject/utils/extra.stx`
(`utils/extra.stx` relative to the current module).  If `extra.stx` specifies
its own relative import, for example:

    import .common

Then the module `common` is expected to be found at `/myproject/utils/common.stx`
(`common.stx` relative to the current module).

To import a module from a parent directory, prefix with two dots:

    import ..common

For a grandparent directory, use three dots (`...common`) etcetera.