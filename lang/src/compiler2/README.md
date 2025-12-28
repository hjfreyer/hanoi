# Compiler

The current pipeline:
- unlinked: functions compiled, but may have external name references.
- linked: all name references resolved, but still contains various layers 
  of indirection.
- bytecode: Ready for the VM to execute.