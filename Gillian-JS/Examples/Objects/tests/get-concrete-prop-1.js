var obj = { p: 1 };
var v1 = obj["p"];
var v2 = obj["u"];
Assert(v1 = 1);
Assert(v2 = undefined);
