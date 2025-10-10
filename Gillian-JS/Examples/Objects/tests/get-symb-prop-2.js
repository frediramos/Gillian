var obj = { p: 1 };
var p_symb = symb_string();
Assume(p_symb = "p");
var v = obj[p_symb];
Assert(v = 1);