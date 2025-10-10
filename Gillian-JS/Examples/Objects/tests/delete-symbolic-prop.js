var p_symb = symb_string();
var obj = { a: 1, b: 2 };
obj[p_symb] = 3;
delete obj[p_symb];
Assume(p_symb = "a");
var v1 = obj["a"];
var v2 = obj["b"];
Assert(v1 = undefined);
Assert(v2 = 2);