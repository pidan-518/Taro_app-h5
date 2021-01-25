/* eslint-disable no-shadow */
/* eslint-disable no-array-constructor */
/* eslint-disable eqeqeq */
const CHAR_TILDE = 126;
const CODE_FNC1 = 102;
const SET_STARTA = 103;
const SET_STARTB = 104;
const SET_STARTC = 105;
const SET_SHIFT = 98;
const SET_CODEA = 101;
const SET_CODEB = 100;
const SET_STOP = 106;
const REPLACE_CODES = {
    CHAR_TILDE: CODE_FNC1 // ~ corresponds to FNC1 in GS1-128 standard
};
const CODESET = {
    ANY: 1,
    AB: 2,
    A: 3,
    B: 4,
    C: 5
};
const PATTERNS = [
    [2, 1, 2, 2, 2, 2, 0, 0],
    [2, 2, 2, 1, 2, 2, 0, 0],
    [2, 2, 2, 2, 2, 1, 0, 0],
    [1, 2, 1, 2, 2, 3, 0, 0],
    [1, 2, 1, 3, 2, 2, 0, 0],
    [1, 3, 1, 2, 2, 2, 0, 0],
    [1, 2, 2, 2, 1, 3, 0, 0],
    [1, 2, 2, 3, 1, 2, 0, 0],
    [1, 3, 2, 2, 1, 2, 0, 0],
    [2, 2, 1, 2, 1, 3, 0, 0],
    [2, 2, 1, 3, 1, 2, 0, 0],
    [2, 3, 1, 2, 1, 2, 0, 0],
    [1, 1, 2, 2, 3, 2, 0, 0],
    [1, 2, 2, 1, 3, 2, 0, 0],
    [1, 2, 2, 2, 3, 1, 0, 0],
    [1, 1, 3, 2, 2, 2, 0, 0],
    [1, 2, 3, 1, 2, 2, 0, 0],
    [1, 2, 3, 2, 2, 1, 0, 0],
    [2, 2, 3, 2, 1, 1, 0, 0],
    [2, 2, 1, 1, 3, 2, 0, 0],
    [2, 2, 1, 2, 3, 1, 0, 0],
    [2, 1, 3, 2, 1, 2, 0, 0],
    [2, 2, 3, 1, 1, 2, 0, 0],
    [3, 1, 2, 1, 3, 1, 0, 0],
    [3, 1, 1, 2, 2, 2, 0, 0],
    [3, 2, 1, 1, 2, 2, 0, 0],
    [3, 2, 1, 2, 2, 1, 0, 0],
    [3, 1, 2, 2, 1, 2, 0, 0],
    [3, 2, 2, 1, 1, 2, 0, 0],
    [3, 2, 2, 2, 1, 1, 0, 0],
    [2, 1, 2, 1, 2, 3, 0, 0],
    [2, 1, 2, 3, 2, 1, 0, 0],
    [2, 3, 2, 1, 2, 1, 0, 0],
    [1, 1, 1, 3, 2, 3, 0, 0],
    [1, 3, 1, 1, 2, 3, 0, 0],
    [1, 3, 1, 3, 2, 1, 0, 0],
    [1, 1, 2, 3, 1, 3, 0, 0],
    [1, 3, 2, 1, 1, 3, 0, 0],
    [1, 3, 2, 3, 1, 1, 0, 0],
    [2, 1, 1, 3, 1, 3, 0, 0],
    [2, 3, 1, 1, 1, 3, 0, 0],
    [2, 3, 1, 3, 1, 1, 0, 0],
    [1, 1, 2, 1, 3, 3, 0, 0],
    [1, 1, 2, 3, 3, 1, 0, 0],
    [1, 3, 2, 1, 3, 1, 0, 0],
    [1, 1, 3, 1, 2, 3, 0, 0],
    [1, 1, 3, 3, 2, 1, 0, 0],
    [1, 3, 3, 1, 2, 1, 0, 0],
    [3, 1, 3, 1, 2, 1, 0, 0],
    [2, 1, 1, 3, 3, 1, 0, 0],
    [2, 3, 1, 1, 3, 1, 0, 0],
    [2, 1, 3, 1, 1, 3, 0, 0],
    [2, 1, 3, 3, 1, 1, 0, 0],
    [2, 1, 3, 1, 3, 1, 0, 0],
    [3, 1, 1, 1, 2, 3, 0, 0],
    [3, 1, 1, 3, 2, 1, 0, 0],
    [3, 3, 1, 1, 2, 1, 0, 0],
    [3, 1, 2, 1, 1, 3, 0, 0],
    [3, 1, 2, 3, 1, 1, 0, 0],
    [3, 3, 2, 1, 1, 1, 0, 0],
    [3, 1, 4, 1, 1, 1, 0, 0],
    [2, 2, 1, 4, 1, 1, 0, 0],
    [4, 3, 1, 1, 1, 1, 0, 0],
    [1, 1, 1, 2, 2, 4, 0, 0],
    [1, 1, 1, 4, 2, 2, 0, 0],
    [1, 2, 1, 1, 2, 4, 0, 0],
    [1, 2, 1, 4, 2, 1, 0, 0],
    [1, 4, 1, 1, 2, 2, 0, 0],
    [1, 4, 1, 2, 2, 1, 0, 0],
    [1, 1, 2, 2, 1, 4, 0, 0],
    [1, 1, 2, 4, 1, 2, 0, 0],
    [1, 2, 2, 1, 1, 4, 0, 0],
    [1, 2, 2, 4, 1, 1, 0, 0],
    [1, 4, 2, 1, 1, 2, 0, 0],
    [1, 4, 2, 2, 1, 1, 0, 0],
    [2, 4, 1, 2, 1, 1, 0, 0],
    [2, 2, 1, 1, 1, 4, 0, 0],
    [4, 1, 3, 1, 1, 1, 0, 0],
    [2, 4, 1, 1, 1, 2, 0, 0],
    [1, 3, 4, 1, 1, 1, 0, 0],
    [1, 1, 1, 2, 4, 2, 0, 0],
    [1, 2, 1, 1, 4, 2, 0, 0],
    [1, 2, 1, 2, 4, 1, 0, 0],
    [1, 1, 4, 2, 1, 2, 0, 0],
    [1, 2, 4, 1, 1, 2, 0, 0],
    [1, 2, 4, 2, 1, 1, 0, 0],
    [4, 1, 1, 2, 1, 2, 0, 0],
    [4, 2, 1, 1, 1, 2, 0, 0],
    [4, 2, 1, 2, 1, 1, 0, 0],
    [2, 1, 2, 1, 4, 1, 0, 0],
    [2, 1, 4, 1, 2, 1, 0, 0],
    [4, 1, 2, 1, 2, 1, 0, 0],
    [1, 1, 1, 1, 4, 3, 0, 0],
    [1, 1, 1, 3, 4, 1, 0, 0],
    [1, 3, 1, 1, 4, 1, 0, 0],
    [1, 1, 4, 1, 1, 3, 0, 0],
    [1, 1, 4, 3, 1, 1, 0, 0],
    [4, 1, 1, 1, 1, 3, 0, 0],
    [4, 1, 1, 3, 1, 1, 0, 0],
    [1, 1, 3, 1, 4, 1, 0, 0],
    [1, 1, 4, 1, 3, 1, 0, 0],
    [3, 1, 1, 1, 4, 1, 0, 0],
    [4, 1, 1, 1, 3, 1, 0, 0],
    [2, 1, 1, 4, 1, 2, 0, 0],
    [2, 1, 1, 2, 1, 4, 0, 0],
    [2, 1, 1, 2, 3, 2, 0, 0],
    [2, 3, 3, 1, 1, 1, 2, 0] // 106
];
function getBytes(str) {
    const bytes = [];
    for (let i = 0; i < str.length; i++) {
        bytes.push(str.charCodeAt(i));
    }
    return bytes;
}
export default function code128(text) {
    const codes = stringToCode128(text);
    let buffer = [];
    for (let i = 0; i < codes.length; i++) {
        const c = codes[i];
        for (let bar = 0; bar < 8; bar += 2) {
            const barLen = PATTERNS[c][bar];
            buffer = buffer.concat(Array(barLen).fill(1));
            const spcLen = PATTERNS[c][bar + 1];
            buffer = buffer.concat(Array(spcLen).fill(0));
        }
    }
    return buffer;
}
function stringToCode128(text) {
    const barc = {
        currcs: CODESET.C
    };
    const bytes = getBytes(text);
    // decide starting codeset
    let index = bytes[0] == CHAR_TILDE ? 1 : 0;
    const csa1 = bytes.length > 0 ? codeSetAllowedFor(bytes[index++]) : CODESET.AB;
    const csa2 = bytes.length > 0 ? codeSetAllowedFor(bytes[index++]) : CODESET.AB;
    barc.currcs = getBestStartSet(csa1, csa2);
    barc.currcs = perhapsCodeC(bytes, barc.currcs);
    // if no codeset changes this will end up with bytes.length+3
    // start, checksum and stop
    let codes = [];
    switch (barc.currcs) {
        case CODESET.A:
            codes.push(SET_STARTA);
            break;
        case CODESET.B:
            codes.push(SET_STARTB);
            break;
        default:
            codes.push(SET_STARTC);
            break;
    }
    for (let i = 0; i < bytes.length; i++) {
        let b1 = bytes[i]; // get the first of a pair
        // should we translate/replace
        if (b1 in REPLACE_CODES) {
            codes.push(REPLACE_CODES[b1]);
            i++; // jump to next
            b1 = bytes[i];
        }
        // get the next in the pair if possible
        const b2 = bytes.length > i + 1 ? bytes[i + 1] : -1;
        codes = codes.concat(codesForChar(b1, b2, barc.currcs));
        // code C takes 2 chars each time
        if (barc.currcs == CODESET.C)
            i++;
    }
    // calculate checksum according to Code 128 standards
    let checksum = codes[0];
    for (let weight = 1; weight < codes.length; weight++) {
        checksum += weight * codes[weight];
    }
    codes.push(checksum % 103);
    codes.push(SET_STOP);
    // encoding should now be complete
    return codes;
    function getBestStartSet(csa1, csa2) {
        // tries to figure out the best codeset
        // to start with to get the most compact code
        let vote = 0;
        vote += csa1 == CODESET.A ? 1 : 0;
        vote += csa1 == CODESET.B ? -1 : 0;
        vote += csa2 == CODESET.A ? 1 : 0;
        vote += csa2 == CODESET.B ? -1 : 0;
        // tie goes to B due to my own predudices
        return vote > 0 ? CODESET.A : CODESET.B;
    }
    function perhapsCodeC(bytes, codeset) {
        for (let i = 0; i < bytes.length; i++) {
            const b = bytes[i];
            if ((b < 48 || b > 57) && b != CHAR_TILDE)
                return codeset;
        }
        return CODESET.C;
    }
    // chr1 is current byte
    // chr2 is the next byte to process. looks ahead.
    function codesForChar(chr1, chr2, currcs) {
        const result = [];
        let shifter = -1;
        if (charCompatible(chr1, currcs)) {
            if (currcs == CODESET.C) {
                if (chr2 == -1) {
                    shifter = SET_CODEB;
                    currcs = CODESET.B;
                }
                else if (chr2 != -1 && !charCompatible(chr2, currcs)) {
                    // need to check ahead as well
                    if (charCompatible(chr2, CODESET.A)) {
                        shifter = SET_CODEA;
                        currcs = CODESET.A;
                    }
                    else {
                        shifter = SET_CODEB;
                        currcs = CODESET.B;
                    }
                }
            }
        }
        else {
            // if there is a next char AND that next char is also not compatible
            if (chr2 != -1 && !charCompatible(chr2, currcs)) {
                // need to switch code sets
                switch (currcs) {
                    case CODESET.A:
                        shifter = SET_CODEB;
                        currcs = CODESET.B;
                        break;
                    case CODESET.B:
                        shifter = SET_CODEA;
                        currcs = CODESET.A;
                        break;
                }
            }
            else {
                // no need to shift code sets, a temporary SHIFT will suffice
                shifter = SET_SHIFT;
            }
        }
        // ok some type of shift is nessecary
        if (shifter != -1) {
            result.push(shifter);
            result.push(codeValue(chr1));
        }
        else {
            if (currcs == CODESET.C) {
                // include next as well
                result.push(codeValue(chr1, chr2));
            }
            else {
                result.push(codeValue(chr1));
            }
        }
        barc.currcs = currcs;
        return result;
    }
}
// reduce the ascii code to fit into the Code128 char table
function codeValue(chr1, chr2 = undefined) {
    if (typeof chr2 === 'undefined') {
        return chr1 >= 32 ? chr1 - 32 : chr1 + 64;
    }
    else {
        return parseInt(String.fromCharCode(chr1) + String.fromCharCode(chr2));
    }
}
function charCompatible(chr, codeset) {
    const csa = codeSetAllowedFor(chr);
    if (csa == CODESET.ANY)
        return true;
    // if we need to change from current
    if (csa == CODESET.AB)
        return true;
    if (csa == CODESET.A && codeset == CODESET.A)
        return true;
    if (csa == CODESET.B && codeset == CODESET.B)
        return true;
    return false;
}
function codeSetAllowedFor(chr) {
    if (chr >= 48 && chr <= 57) {
        // 0-9
        return CODESET.ANY;
    }
    else if (chr >= 32 && chr <= 95) {
        // 0-9 A-Z
        return CODESET.AB;
    }
    else {
        // if non printable
        return chr < 32 ? CODESET.A : CODESET.B;
    }
}
//# sourceMappingURL=code128.js.map