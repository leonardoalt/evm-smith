pragma circom 2.0.0;

// The minimal circuit this demo tests against: prove knowledge of a private
// x such that y = x*x, with y the (one) public input/output. Chosen so the
// circuit has exactly nPublic = 1, matching the one-public-input layout
// Program.lean hard-codes (no dynamic-array calldata decoding needed).
template Square() {
    signal input x;
    signal output y;
    y <== x * x;
}

component main = Square();
