// Implementation of DES from Understanding Cryptography.
// Additional resources:
// - https://www.geeksforgeeks.org/data-encryption-standard-des-set-1/
// - http://page.math.tu-berlin.de/~kant/teaching/hess/krypto-ws2006/des.htm
// - https://github.com/kongfy/DES/blob/master/des.c
// - https://people.csail.mit.edu/rivest/pubs/Riv85.txt

open System

// DES uses 4-bit, 6-bit, 32-bit, 48-bit, 56-bit, and 64-bit blocks.
// In our implementation blocks are stored as `uint64` values.
// Each block is stored in the lowest bits of `uint64`.
// The highest bits of `uint64` which are not used by a block are zero.
//
// Bits of each block are numbered from left to right starting with 1.
//
// Example: A block with 48 bits.
// The first 16 highest bits of `uint64` are zero.
// They are followed by 48 bits of the block.
// The 17th highest bit of `uint64` is the first bit of the block - this bit has the number 1.
// The lowest bit of `uint64` is the last bit of the block - this bit has the number 48.

/// This type represents a permutation of a block.
///
/// A permutation is represented by a table.
/// The n-th item of the table is a position of the input bit which will become the n-th output bit.
/// The size of the table is the size of the output block.
///
/// A size of the input block must be explicitly specified
/// because without it we can't know where the input block starts in `uint64` value.
type Permutation = Permutation of inputSize:int * table:int[]

module Permutation =
    let make (inputSize : int) (table : int[]) =
        // Having input size or output size 0 doesn't make much sense.
        if inputSize < 1 || inputSize > 64 then
            failwith "Input size must be between 1 and 64"
        if table.Length < 1 || table.Length > 64 then
            failwith "Output size (table size) must be between 1 and 64"
        table |> Array.iter (fun pos ->
            if pos < 1 || pos > inputSize then
                failwith "Positions must be between 1 and input size")
        Permutation (inputSize, table)

    let apply (Permutation (inputSize, table)) (x : uint64) =
        let mutable res = 0UL
        for pos in table do
            res <- (res <<< 1) ||| (x >>> (inputSize - pos) &&& 1UL)
        res

    let invert (Permutation (inputSize, table)) =
        if inputSize <> table.Length then
            failwith "Permutation where input size <> output size cannot be inverted"
        let table' = Array.init inputSize (fun i ->
            // Ensures that each position appears exactly once in `table`
            // (because `findIndex` raises when the item is not found).
            Array.findIndex ((=) (i + 1)) table + 1)
        Permutation (inputSize, table')

let initialPermutation = Permutation.make 64 [|
    58; 50; 42; 34; 26; 18; 10; 2
    60; 52; 44; 36; 28; 20; 12; 4
    62; 54; 46; 38; 30; 22; 14; 6
    64; 56; 48; 40; 32; 24; 16; 8
    57; 49; 41; 33; 25; 17; 9; 1
    59; 51; 43; 35; 27; 19; 11; 3
    61; 53; 45; 37; 29; 21; 13; 5
    63; 55; 47; 39; 31; 23; 15; 7
|]

let fromHex (hex : string) : uint64 = Convert.ToUInt64(hex, 16)

let toHex (x : uint64) = $"%X{x}"

let check (input : string) (expected : string) (f : uint64 -> uint64) =
    let actual =
        fromHex input
        |> f
        |> toHex
    if  actual <> expected then
        failwith $"Error %s{actual} <> %s{expected}"

let ``test - initial permutation`` =
    check "123456ABCD132536" "14A7D67818CA18AD" (Permutation.apply initialPermutation)

let finalPermutation = Permutation.invert initialPermutation

let ``test - final permutation is inverse of initial permutation`` =
    check "123456ABCD132536" "123456ABCD132536"
        (Permutation.apply initialPermutation >> Permutation.apply finalPermutation)

let expansionPermutation = Permutation.make 32 [|
    32; 1; 2; 3; 4; 5; 4; 5
    6; 7; 8; 9; 8; 9; 10; 11
    12; 13; 12; 13; 14; 15; 16; 17
    16; 17; 18; 19; 20; 21; 20; 21
    22; 23; 24; 25; 24; 25; 26; 27
    28; 29; 28; 29; 30; 31; 32; 1
|]

let ``test - apply works with blocks having less than 64 bits`` =
    check "F0AAF0AA" "7A15557A1555" (Permutation.apply expansionPermutation)

let pPermutation = Permutation.make 32 [|
    16; 7; 20; 21; 29; 12; 28; 17
    1; 15; 23; 26; 5; 18; 31; 10
    2; 8; 24; 14; 32; 27; 3; 9
    19; 13; 30; 6; 22; 11; 4; 25
|]

/// Table with 4 rows and 16 columns.
///
/// Used for transforming 6 bit numbers into 4 bit numbers.
type SBox = SBox of int[,]

module SBox =
    // TODO Check that every row contains unique numbers within 0-15.
    let make (table : int[,]) =
        if table.GetLength 0 <> 4 || table.GetLength 1 <> 16 then
            failwith "Dimensions of s-box table must be 4 x 16"
        SBox table

    /// Maps 6 bit number to 4 bit number.
    let apply (SBox table) (x : uint64) =
        if x >>> 6 <> 0UL then
            failwith "Input has more than 6 bits"
        // Bits 6, 1 say which row.
        let row = int ((x >>> 4 &&& 2UL) ||| (x &&& 1UL))
        // Bits 5-2 say which column.
        let column = int (x >>> 1 &&& 15UL)
        uint64 table.[row, column]

let sBoxes = Array.map SBox.make [|
    array2D [
        [ 14; 4; 13; 1; 2; 15; 11; 8; 3; 10; 6; 12; 5; 9; 0; 7 ]
        [ 0; 15; 7; 4; 14; 2; 13; 1; 10; 6; 12; 11; 9; 5; 3; 8 ]
        [ 4; 1; 14; 8; 13; 6; 2; 11; 15; 12; 9; 7; 3; 10; 5; 0 ]
        [ 15; 12; 8; 2; 4; 9; 1; 7; 5; 11; 3; 14; 10; 0; 6; 13 ]
    ]
    array2D [
        [ 15; 1; 8; 14; 6; 11; 3; 4; 9; 7; 2; 13; 12; 0; 5; 10 ]
        [ 3; 13; 4; 7; 15; 2; 8; 14; 12; 0; 1; 10; 6; 9; 11; 5 ]
        [ 0; 14; 7; 11; 10; 4; 13; 1; 5; 8; 12; 6; 9; 3; 2; 15 ]
        [ 13; 8; 10; 1; 3; 15; 4; 2; 11; 6; 7; 12; 0; 5; 14; 9 ]
    ]
    array2D [
        [ 10; 0; 9; 14; 6; 3; 15; 5; 1; 13; 12; 7; 11; 4; 2; 8 ]
        [ 13; 7; 0; 9; 3; 4; 6; 10; 2; 8; 5; 14; 12; 11; 15; 1 ]
        [ 13; 6; 4; 9; 8; 15; 3; 0; 11; 1; 2; 12; 5; 10; 14; 7 ]
        [ 1; 10; 13; 0; 6; 9; 8; 7; 4; 15; 14; 3; 11; 5; 2; 12 ]
    ]
    array2D [
        [ 7; 13; 14; 3; 0; 6; 9; 10; 1; 2; 8; 5; 11; 12; 4; 15 ]
        [ 13; 8; 11; 5; 6; 15; 0; 3; 4; 7; 2; 12; 1; 10; 14; 9 ]
        [ 10; 6; 9; 0; 12; 11; 7; 13; 15; 1; 3; 14; 5; 2; 8; 4 ]
        [ 3; 15; 0; 6; 10; 1; 13; 8; 9; 4; 5; 11; 12; 7; 2; 14 ]
    ]
    array2D [
        [ 2; 12; 4; 1; 7; 10; 11; 6; 8; 5; 3; 15; 13; 0; 14; 9 ]
        [ 14; 11; 2; 12; 4; 7; 13; 1; 5; 0; 15; 10; 3; 9; 8; 6 ]
        [ 4; 2; 1; 11; 10; 13; 7; 8; 15; 9; 12; 5; 6; 3; 0; 14 ]
        [ 11; 8; 12; 7; 1; 14; 2; 13; 6; 15; 0; 9; 10; 4; 5; 3 ]
    ]
    array2D [
        [ 12; 1; 10; 15; 9; 2; 6; 8; 0; 13; 3; 4; 14; 7; 5; 11 ]
        [ 10; 15; 4; 2; 7; 12; 9; 5; 6; 1; 13; 14; 0; 11; 3; 8 ]
        [ 9; 14; 15; 5; 2; 8; 12; 3; 7; 0; 4; 10; 1; 13; 11; 6 ]
        [ 4; 3; 2; 12; 9; 5; 15; 10; 11; 14; 1; 7; 6; 0; 8; 13 ]
    ]
    array2D [
        [ 4; 11; 2; 14; 15; 0; 8; 13; 3; 12; 9; 7; 5; 10; 6; 1 ]
        [ 13; 0; 11; 7; 4; 9; 1; 10; 14; 3; 5; 12; 2; 15; 8; 6 ]
        [ 1; 4; 11; 13; 12; 3; 7; 14; 10; 15; 6; 8; 0; 5; 9; 2 ]
        [ 6; 11; 13; 8; 1; 4; 10; 7; 9; 5; 0; 15; 14; 2; 3; 12 ]
    ]
    array2D [
        [ 13; 2; 8; 4; 6; 15; 11; 1; 10; 9; 3; 14; 5; 0; 12; 7 ]
        [ 1; 15; 13; 8; 10; 3; 7; 4; 12; 5; 6; 11; 0; 14; 9; 2 ]
        [ 7; 11; 4; 1; 9; 12; 14; 2; 0; 6; 10; 13; 15; 3; 5; 8 ]
        [ 2; 1; 14; 7; 4; 10; 8; 13; 15; 12; 9; 0; 3; 5; 6; 11 ]
    ]
|]

let ``test - check S-box 1`` =
    let expected = 8UL
    let actual = SBox.apply sBoxes.[0] 0b100101UL
    if  actual <> expected then
        failwith $"Error %X{actual} <> %X{expected}"

/// Initial key permutation.
/// Convert 64-bit key to 56-bit key
/// by ignoring 8 parity bits.
let pc1Permutation = Permutation.make 64 [|
    57; 49; 41; 33; 25; 17; 9; 1
    58; 50; 42; 34; 26; 18; 10; 2
    59; 51; 43; 35; 27; 19; 11; 3
    60; 52; 44; 36; 63; 55; 47; 39
    31; 23; 15; 7; 62; 54; 46; 38
    30; 22; 14; 6; 61; 53; 45; 37
    29; 21; 13; 5; 28; 20; 12; 4
|]

/// Final permutation for creating round key.
/// Permuted choice 2.
/// From 56-bit input block creates 48-bit round key.
let pc2Permutation = Permutation.make 56 [|
    14; 17; 11; 24; 1; 5; 3; 28
    15; 6; 21; 10; 23; 19; 12; 4
    26; 8; 16; 7; 27; 20; 13; 2
    41; 52; 31; 37; 47; 55; 30; 40
    51; 45; 33; 48; 44; 49; 39; 56
    34; 53; 46; 42; 50; 36; 29; 32
|]

/// We can understand `fFunc` as a pseudorandom generator
/// with two inputs `r` and `roundKey`.
/// Its output is used to encrypt `l`.
///
/// In DES `fFunc` is a surjective function.
///
/// `r` has 32 bits and `roundKey` has 48 bits.
let fFunc (r : uint64) (roundKey : uint64) =
    // Expand 32-bit input to 48 bits.
    let afterExpansion = Permutation.apply expansionPermutation r
    let xored = afterExpansion ^^^ roundKey

    // Feed eight 6-bit blocks to s-boxes to get
    // eight 4-bit blocks.
    let mutable afterSBoxes = 0UL
    for i = 1 to 8 do
        let inputBlock = xored >>> (6 * (8 - i)) &&& 63UL
        let outputBlock = SBox.apply sBoxes.[i - 1] inputBlock
        afterSBoxes <- (afterSBoxes <<< 4) ||| outputBlock

    Permutation.apply pPermutation afterSBoxes

let feistelNetwork (input : uint64) (roundKeys : uint64[]) =
    let mask32 = 0xFFFFFFFFUL
    let mutable l = input >>> 32 &&& mask32
    let mutable r = input &&& mask32

    for round = 0 to 15 do
        let newL = r
        let newR = l ^^^ fFunc r roundKeys.[round]
        l <- newL
        r <- newR

    // Swap halves `l` and `r` and combine them.
    (r <<< 32) ||| l

let computeRoundKeysForEncryption (key : uint64) : uint64[] =
    let mask28 = 0xFFFFFFFUL
    // Rotate left by 1 within 28 bits.
    let rotateLeft1 (x : uint64) =
        if x >>> 27 <> 0UL
        then x <<< 1 ||| 1UL &&& mask28
        else x <<< 1
    let rotateLeft2 = rotateLeft1 >> rotateLeft1

    // Throw away 8 parity bits. 64-bit key is converted to 56-bit key.
    let afterPc1 = Permutation.apply pc1Permutation key
    // Split 56-bit key into halves.
    let mutable c = afterPc1 >>> 28
    let mutable d = afterPc1 &&& mask28

    // Calculate 16 round keys.
    Array.init 16 (fun round ->
        let rotate =
            match round with
            // Rotate by 1.
            | 0 | 1 | 8 | 15 -> rotateLeft1
            | _ -> rotateLeft2
        c <- rotate c
        d <- rotate d
        // Combine halves and generate key for round `round`.
        Permutation.apply pc2Permutation (c <<< 28 ||| d))

let crypt (plainText : uint64) (roundKeys : uint64[]) =
    let afterIp = Permutation.apply initialPermutation plainText
    let afterFeistelNet = feistelNetwork afterIp roundKeys
    let afterFp = Permutation.apply finalPermutation afterFeistelNet
    afterFp

let encrypt plainText key = crypt plainText (computeRoundKeysForEncryption key)
let decrypt plainText key = crypt plainText (computeRoundKeysForEncryption key |> Array.rev)

let ``test - validate DES`` =
    let expected = [|
        "8DA744E0C94E5E17"; "0CDB25E3BA3C6D79"
        "4784C4BA5006081F"; "1CF1FC126F2EF842"
        "E4BE250042098D13"; "7BFC5DC6ADB5797C"
        "1AB3B4D82082FB28"; "C1576A14DE707097"
        "739B68CD2E26782A"; "2A59F0C464506EDB"
        "A5C39D4251F0A81E"; "7239AC9A6107DDB1"
        "070CAC8590241233"; "78F87B6E3DFECF61"
        "95EC2578C2C433F0"; "1B1A2DDB4C642438"
    |]
    let mutable result = 0x9474B8E8C73BCA7DUL
    for i = 0 to 15 do
        result <-
            if i % 2 = 0
            then encrypt result result
            else decrypt result result
        //printfn $"X%d{i + 1}: %X{result}"
        if toHex result <> expected.[i].TrimStart('0') then
            failwith $"Error %X{result} <> %s{expected.[i]}"

[<EntryPoint>]
let main argv =
    let key = fromHex "AABB09182736CCDD"

    let plainText = fromHex "123456ABCD132536"
    printfn "Plain text text %X" plainText

    let cipherText = encrypt plainText key
    printfn "Cipher text %X" cipherText

    let decryptedText = decrypt cipherText key
    printfn "Decrypted text %X" decryptedText

    0
