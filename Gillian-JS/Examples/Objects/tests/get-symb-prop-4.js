var p_symb = symb_string();
var obj = { a: 1, b: 2 };
var v = obj[p_symb];
Assume(p_symb = "b");
Assert(v = 2);