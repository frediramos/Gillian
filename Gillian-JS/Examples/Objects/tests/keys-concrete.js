var obj = { a: 1, b: 2 };
var keys = Object.keys(obj);
var a = keys[0];
var b = keys[1];
Assert(a = "a");
Assert(b = "b");