(function () {
    'use strict';

    const supports_wasm = typeof WebAssembly === 'object' &&
        typeof WebAssembly.validate === 'function';

    if (supports_wasm) {
        let memory = new WebAssembly.Memory({ initial: 0 });

        function fromCString(ptr, len) {
            let utf8Decoder = new TextDecoder("UTF-8");
            let strBuf = new Uint8Array(memory.buffer, ptr, len);
            return utf8Decoder.decode(strBuf);
        }

        const importObject = {
            imports: {
                memory: memory,
                opt_proto_js_exit: code => { throw new Error('exit(' + code + ')') },
                opt_proto_js_print: (ptr, len) => console.log(fromCString(ptr, len)),
                opt_proto_js_print_error: (ptr, len) => console.error(fromCString(ptr, len)),
                opt_proto_js_memory_size: () => memory.buffer.byteLength,
                opt_proto_js_memory_grow: delta => memory.grow(delta)
            }
        };

        const { instance } = await WebAssembly.instantiateStreaming(fetch('a.wasm'), importObject);
    } else {
        alert("This browser does not support WebAssembly!");
    }
})();