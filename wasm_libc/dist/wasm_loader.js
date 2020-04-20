(function () {
    'use strict';
    const has_wasm = typeof WebAssembly === 'object' && typeof WebAssembly.validate === 'function';
    if (has_wasm) {
        const importObject = {
            imports: {
                print: arg => console.log(arg),
                print_error: arg => console.error(arg),
                abort: () => console.log("abort is an illusion")
            }
        };
        const { instance } = await WebAssembly.instantiateStreaming(fetch('a.wasm'), importObject);
    } else {
        alert("This browser does not support WebAssembly!");
    }
})();