(function () {
    'use strict';

    const supportsWasm = typeof WebAssembly === 'object' &&
        typeof WebAssembly.validate === 'function';

    if (supportsWasm) {
        /* We will capture memory from the instance exports. */
        let memory = null;

        function escapeHtml(unsafe) {
            return unsafe
                .replace(/&/g, "&amp;")
                .replace(/</g, "&lt;")
                .replace(/>/g, "&gt;")
                .replace(/"/g, "&quot;")
                .replace(/'/g, "&#039;");
        }

        function fromCString(ptr, len) {
            let utf8Decoder = new TextDecoder('UTF-8');
            let strBuffer = new Uint8Array(memory.buffer, ptr, len);
            return utf8Decoder.decode(strBuffer);
        }

        function print(ptr, len) {
            let str = escapeHtml(fromCString(ptr, len));
            document.getElementById('outputBox').innerHTML += str;
        }

        function printError(ptr, len) {
            let str = "<span style='color:red';>" + escapeHtml(fromCString(ptr, len)) + '</span>';
            document.getElementById("outputBox").innerHTML += str;
        }

        let getChar = (function () {
            let strBuffer = "";
            let curChar = 1;

            return function () {
                if (curChar > strBuffer.length) {
                    strBuffer = prompt('Input requested:');
                    // 'prompt()' returns 'null' when the user clicks 'cancel'.
                    if (strBuffer == null) {
                        strBuffer = "";
                    }
                    curChar = 0;
                }
                /* This check has to come after the (curChar > strBuffer.length)
                   check in case prompt() returns a length 0 string. */
                if (curChar == strBuffer.length) {
                    curChar += 1;
                    return "\n".charCodeAt(0);
                }

                const char = strBuffer.charCodeAt(curChar++);
                if (char < 0x100) {
                    return char;
                } else {
                    return '?'.charCodeAt(0);
                }
            };
        })();

        function rand() {
            const POW = Math.pow(2, 63);
            const MAX = POW - 1;
            const MIN = -POW;
            return Math.floor(Math.random() * (MAX - MIN) + MIN);
        }

        /* `morphic_js_memory_size` and `morphic_js_memory_grow` are provided
           to the tal implementation via JavaScript rather than WebAssembly
           intrinsics to avoid needing to compile any WAT files. */
        const imports = {
            env: {
                morphic_js_exit: code => { throw new Error('exit(' + code + ')') },
                morphic_js_get_char: getChar,
                morphic_js_rand: rand,
                morphic_js_print: print,
                morphic_js_print_error: printError,
                morphic_js_memory_size: () => memory.buffer.byteLength,
                morphic_js_memory_grow: delta => memory.grow(delta)
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
