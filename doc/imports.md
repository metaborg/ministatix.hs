# Imports
To import another module, use the `import` directive, or the `:import` (or `:i`)
command in the REPL.  The name of the module is specified in _dotted notation_:
a sequence of names separated by dots.  The import ends with a semi-colon.
For example:

    import utils.extra

Will import the file `utils/extra.stx` relative to the base directory,
which is the project root or the current working directory when in a REPL.
