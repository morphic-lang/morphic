(module
  (memory (import "imports" "memory") 1)
  (func (export "__wasm_builtin_memory_size") (result i32)
    memory.size)
  (func (export "__wasm_builtin_memory_grow") (param i32) (result i32)
    local.get 0
    memory.grow))