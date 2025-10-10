var obj = {};

var a_symb = symb_string();
var b_symb = symb_string();
obj[a_symb] = 1;
obj[b_symb] = 2;

var keys = Object.keys(obj);
var a = keys[0];
var b = keys[1];
Assert(a = a_symb);
Assert(b = b_symb);