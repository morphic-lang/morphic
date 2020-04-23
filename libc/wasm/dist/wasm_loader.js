(function () {
    'use strict';

    const supportsWasm = typeof WebAssembly === 'object' &&
        typeof WebAssembly.validate === 'function';

    if (supportsWasm) {
        /* We will capture memory from the instance exports. */
        let memory = null;

        function fromCString(ptr, len) {
            let utf8Decoder = new TextDecoder('UTF-8');
            let strBuffer = new Uint8Array(memory.buffer, ptr, len);
            return utf8Decoder.decode(strBuffer);
        }

        let getChar = (function () {
            /* Make sure that this value matches on the C side. */
            const EOF = -1;
            let strBuffer = "";
            let curChar = 1;

            return function () {
                if (curChar > strBuffer.length) {
                    strBuffer = prompt('Input requested:');
                    curChar = 0;
                }
                /* This check has to come after the (curChar > strBuffer.length)
                   check in case prompt() returns a length 0 string. */
                if (curChar == strBuffer.length) {
                    curChar += 1;
                    return EOF;
                }
                return strBuffer[curChar++];
            };
        })();

        /* `opt_proto_js_memory_size` and `opt_proto_js_memory_grow` are
            provided to the libc implementation via JavaScript rather than
            WebAssembly intrinsics to avoid needing to compile any WAT files. */
        const imports = {
            env: {
                opt_proto_js_exit: code => { throw new Error('exit(' + code + ')') },
                opt_proto_js_get_char: getChar,
                opt_proto_js_print: (ptr, len) => console.log(fromCString(ptr, len)),
                opt_proto_js_print_error: (ptr, len) => console.error(fromCString(ptr, len)),
                opt_proto_js_memory_size: () => memory.buffer.byteLength,
                opt_proto_js_memory_grow: delta => memory.grow(delta)
            }
        };

        WebAssembly.instantiateStreaming(fetch('a.wasm'), imports).then(results => {
            memory = results.instance.exports.memory;
            results.instance.exports._start();
        });
    } else {
        alert('This browser does not support WebAssembly!');
    }
})();