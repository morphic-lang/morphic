(function () {
    'use strict';
    const has_wasm = typeof WebAssembly === 'object' && typeof WebAssembly.validate === 'function';
    if (has_wasm) {
        const importObject = {
            imports: {
                memory: new WebAssembly.Memory({ initial: 1 }),
                print: arg => console.log(arg),
                print_error: arg => console.error(arg),
                abort: () => { throw new Error('abort') }
            }
        };
        const { instance } = await WebAssembly.instantiateStreaming(fetch('a.wasm'), importObject);
    } else {
        alert("This browser does not support WebAssembly!");
    }
})();