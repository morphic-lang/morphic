(function () {
    'use strict';

    const supportsWasm = typeof WebAssembly === 'object' &&
        typeof WebAssembly.validate === 'function';

    if (supportsWasm) {
        let memory = new WebAssembly.Memory({ initial: 0 });

        function fromCString(ptr, len) {
            let utf8Decoder = new TextDecoder('UTF-8');
            let strBuf = new Uint8Array(memory.buffer, ptr, len);
            return utf8Decoder.decode(strBuf);
        }

        let getChar = (function () {
            /* Make sure that this value matches on the C side. */
            const EOF = -1;

            let strBuf = "";
            let curChar = 1;

            return function () {
                if (curChar > strBuf.length) {
                    strBuf = prompt('Input requested:');
                    curChar = 0;
                }
                /* This check has to come after the (curChar > strBuf.length)
                   check in case prompt() returns a length 0 string. */
                if (curChar == strBuf.length) {
                    curChar += 1;
                    return EOF;
                }
                return strBuf[curChar++];
            };
        })();

        const importObject = {
            imports: {
                memory: memory,
                opt_proto_js_exit: code => { throw new Error('exit(' + code + ')') },
                opt_proto_js_get_char: getChar,
                opt_proto_js_print: (ptr, len) => console.log(fromCString(ptr, len)),
                opt_proto_js_print_error: (ptr, len) => console.error(fromCString(ptr, len)),
                opt_proto_js_memory_size: () => memory.buffer.byteLength,
                opt_proto_js_memory_grow: delta => memory.grow(delta)
            }
        };

        WebAssembly.instantiateStreaming(fetch('a.wasm'), importObject).then(results => {
            results.instance.exports.opt_proto_start();
        });
    } else {
        alert('This browser does not support WebAssembly!');
    }
})();