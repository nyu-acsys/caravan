let identity value = value
let choose ?(value = identity 42) = function () -> identity value
