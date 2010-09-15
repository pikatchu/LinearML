

module Test: sig

  type t = 
    | A
    | AA
    | AAA
    | AAAA
    | AAAAA
    | AAAAAA
    | AAAAAAA
    | AAAAAAAA
    | AAAAAAAAA
    | AAAAAAAAAA
    | AAAAAAAAAAA
    | AAAAAAAAAAAA
    | AAAAAAAAAAAAA
    | AAAAAAAAAAAAAA
    | AAAAAAAAAAAAAAA
    | AAAAAAAAAAAAAAAA
    | AAAAAAAAAAAAAAAAA
    | AAAAAAAAAAAAAAAAAA
    | AAAAAAAAAAAAAAAAAAA
    | AAAAAAAAAAAAAAAAAAAA
    | AAAAAAAAAAAAAAAAAAAAA
    | B
    | BB
    | BBB
    | BBBB
    | BBBBB
    | BBBBBB
    | BBBBBBB
    | BBBBBBBB
    | BBBBBBBBB
    | BBBBBBBBBB
    | BBBBBBBBBBB
    | BBBBBBBBBBBB
    | BBBBBBBBBBBBB
    | BBBBBBBBBBBBBB
    | BBBBBBBBBBBBBBB
    | BBBBBBBBBBBBBBBB
    | BBBBBBBBBBBBBBBBB
    | BBBBBBBBBBBBBBBBBB
    | BBBBBBBBBBBBBBBBBBB
    | BBBBBBBBBBBBBBBBBBBB
    | BBBBBBBBBBBBBBBBBBBBB

  val f: t obs -> int32


end = struct


  let rec f t =
    match t, t, t with
    | A, _, A -> 0
    | _, AA, A -> 0
    | AAA, A, _ -> 0
    | AAAA, _, A -> 0
    | _, AAAAA, A -> 0
    | AAAAAA, A, _ -> 0
    | AAAAAAA, _, A -> 0
    | _, AAAAAAAA, A -> 0
    | AAAAAAAAA, A, _ -> 0
    | AAAAAAAAAA, _, A -> 0
    | _, AAAAAAAAAAA, A -> 0
    | AAAAAAAAAAAA, A, _ -> 0
    | AAAAAAAAAAAAA, _, A -> 0
    | _, AAAAAAAAAAAAAA, A -> 0
    | AAAAAAAAAAAAAAA, A, _ -> 0
    | AAAAAAAAAAAAAAAA, _, A -> 0
    | _, AAAAAAAAAAAAAAAAA, A -> 0
    | AAAAAAAAAAAAAAAAAA, A, _ -> 0
    | AAAAAAAAAAAAAAAAAAA, _, A -> 0
    | _, AAAAAAAAAAAAAAAAAAAA, A -> 0

    | B, A, _ -> 0
    | BB, _, A -> 0
    | _, BBB, A -> 0
    | BBBB, A, _ -> 0
    | BBBBB, _, A -> 0
    | _, BBBBBB, A -> 0
    | BBBBBBB, A, _ -> 0
    | BBBBBBBB, _, A -> 0
    | _, BBBBBBBBB, A -> 0
    | BBBBBBBBBB, A, _ -> 0
    | BBBBBBBBBBB, _, A -> 0
    | _, BBBBBBBBBBBB, A -> 0
    | BBBBBBBBBBBBB, A, _ -> 0
    | BBBBBBBBBBBBBB, _, A -> 0
    | _, BBBBBBBBBBBBBBB, A -> 0
    | BBBBBBBBBBBBBBBB, A, _ -> 0
    | BBBBBBBBBBBBBBBBB, _, A -> 0
    | _, BBBBBBBBBBBBBBBBBB, A -> 0
    | BBBBBBBBBBBBBBBBBBB, A, _ -> 0
    | BBBBBBBBBBBBBBBBBBBB, _, A -> 0

    | _, A, B -> 0
    | AA, B, _ -> 0
    | AAA, _, B -> 0
    | _, AAAA, B -> 0
    | AAAAA, B, _ -> 0
    | AAAAAA, _, B -> 0
    | _, AAAAAAA, B -> 0
    | AAAAAAAA, B, _ -> 0
    | AAAAAAAAA, _, B -> 0
    | _, AAAAAAAAAA, B -> 0
    | AAAAAAAAAAA, B, _ -> 0
    | AAAAAAAAAAAA, _, B -> 0
    | _, AAAAAAAAAAAAA, B -> 0
    | AAAAAAAAAAAAAA, B, _ -> 0
    | AAAAAAAAAAAAAAA, _, B -> 0
    | _, AAAAAAAAAAAAAAAA, B -> 0
    | AAAAAAAAAAAAAAAAA, B, _ -> 0
    | AAAAAAAAAAAAAAAAAA, _, B -> 0
    | _, AAAAAAAAAAAAAAAAAAA, B -> 0
    | AAAAAAAAAAAAAAAAAAAA, B, _ -> 0

    | B, _, B -> 0
    | _, BB, B -> 0
    | BBB, B, _ -> 0
    | BBBB, _, B -> 0
    | _, BBBBB, B -> 0
    | BBBBBB, B, _ -> 0
    | BBBBBBB, _, B -> 0
    | _, BBBBBBBB, B -> 0
    | BBBBBBBBB, B, _ -> 0
    | BBBBBBBBBB, _, B -> 0
    | _, BBBBBBBBBBB, B -> 0
    | BBBBBBBBBBBB, B, _ -> 0
    | BBBBBBBBBBBBB, _, B -> 0
    | _, BBBBBBBBBBBBBB, B -> 0
    | BBBBBBBBBBBBBBB, B, _ -> 0
    | BBBBBBBBBBBBBBBB, _, B -> 0
    | _, BBBBBBBBBBBBBBBBB, B -> 0
    | BBBBBBBBBBBBBBBBBB, B, _ -> 0
    | BBBBBBBBBBBBBBBBBBB, _, B -> 0
    | _, BBBBBBBBBBBBBBBBBBBB, B -> 0

    | A, BB, _ -> 0
    | AA, _, BB -> 0
    | _, AAA, BB -> 0
    | AAAA, BB, _ -> 0
    | AAAAA, _, BB -> 0
    | _, AAAAAA, BB -> 0
    | AAAAAAA, BB, _ -> 0
    | AAAAAAAA, _, BB -> 0
    | _, AAAAAAAAA, BB -> 0
    | AAAAAAAAAA, BB, _ -> 0
    | AAAAAAAAAAA, _, BB -> 0
    | _, AAAAAAAAAAAA, BB -> 0
    | AAAAAAAAAAAAA, BB, _ -> 0
    | AAAAAAAAAAAAAA, _, BB -> 0
    | _, AAAAAAAAAAAAAAA, BB -> 0
    | AAAAAAAAAAAAAAAA, BB, _ -> 0
    | AAAAAAAAAAAAAAAAA, _, BB -> 0
    | _, AAAAAAAAAAAAAAAAAA, BB -> 0
    | AAAAAAAAAAAAAAAAAAA, BB, _ -> 0
    | AAAAAAAAAAAAAAAAAAAA, _, BB -> 0

    | _, B, BB -> 0
    | BB, BB, _ -> 0
    | BBB, _, BB -> 0
    | _, BBBB, BB -> 0
    | BBBBB, BB, _ -> 0
    | BBBBBB, _, BB -> 0
    | _, BBBBBBB, BB -> 0
    | BBBBBBBB, BB, _ -> 0
    | BBBBBBBBB, _, BB -> 0
    | _, BBBBBBBBBB, BB -> 0
    | BBBBBBBBBBB, BB, _ -> 0
    | BBBBBBBBBBBB, _, BB -> 0
    | _, BBBBBBBBBBBBB, BB -> 0
    | BBBBBBBBBBBBBB, BB, _ -> 0
    | BBBBBBBBBBBBBBB, _, BB -> 0
    | _, BBBBBBBBBBBBBBBB, BB -> 0
    | BBBBBBBBBBBBBBBBB, BB, _ -> 0
    | BBBBBBBBBBBBBBBBBB, _, BB -> 0
    | _, BBBBBBBBBBBBBBBBBBB, BB -> 0
    | BBBBBBBBBBBBBBBBBBBB, BB, _ -> 0

    | A, _, BBB -> 0
    | _, AA, BBB -> 0
    | AAA, BBB, _ -> 0
    | AAAA, _, BBB -> 0
    | _, AAAAA, BBB -> 0
    | AAAAAA, BBB, _ -> 0
    | AAAAAAA, _, BBB -> 0
    | _, AAAAAAAA, BBB -> 0
    | AAAAAAAAA, BBB, _ -> 0
    | AAAAAAAAAA, _, BBB -> 0
    | _, AAAAAAAAAAA, BBB -> 0
    | AAAAAAAAAAAA, BBB, _ -> 0
    | AAAAAAAAAAAAA, _, BBB -> 0
    | _, AAAAAAAAAAAAAA, BBB -> 0
    | AAAAAAAAAAAAAAA, BBB, _ -> 0
    | AAAAAAAAAAAAAAAA, _, BBB -> 0
    | _, AAAAAAAAAAAAAAAAA, BBB -> 0
    | AAAAAAAAAAAAAAAAAA, BBB, _ -> 0
    | AAAAAAAAAAAAAAAAAAA, _, BBB -> 0
    | _, AAAAAAAAAAAAAAAAAAAA, BBB -> 0

    | B, BBB, _ -> 0
    | BB, _, BBB -> 0
    | _, BBB, BBB -> 0
    | BBBB, BBB, _ -> 0
    | BBBBB, _, BBB -> 0
    | _, BBBBBB, BBB -> 0
    | BBBBBBB, BBB, _ -> 0
    | BBBBBBBB, _, BBB -> 0
    | _, BBBBBBBBB, BBB -> 0
    | BBBBBBBBBB, BBB, _ -> 0
    | BBBBBBBBBBB, _, BBB -> 0
    | _, BBBBBBBBBBBB, BBB -> 0
    | BBBBBBBBBBBBB, BBB, _ -> 0
    | BBBBBBBBBBBBBB, _, BBB -> 0
    | _, BBBBBBBBBBBBBBB, BBB -> 0
    | BBBBBBBBBBBBBBBB, BBB, _ -> 0
    | BBBBBBBBBBBBBBBBB, _, BBB -> 0
    | _, BBBBBBBBBBBBBBBBBB, BBB -> 0
    | BBBBBBBBBBBBBBBBBBB, BBB, _ -> 0
    | BBBBBBBBBBBBBBBBBBBB, _, BBB -> 0

    | _, A, BBBB -> 0
    | AA, BBBB, _ -> 0
    | AAA, _, BBBB -> 0
    | _, AAAA, BBBB -> 0
    | AAAAA, BBBB, _ -> 0
    | AAAAAA, _, BBBB -> 0
    | _, AAAAAAA, BBBB -> 0
    | AAAAAAAA, BBBB, _ -> 0
    | AAAAAAAAA, _, BBBB -> 0
    | _, AAAAAAAAAA, BBBB -> 0
    | AAAAAAAAAAA, BBBB, _ -> 0
    | AAAAAAAAAAAA, _, BBBB -> 0
    | _, AAAAAAAAAAAAA, BBBB -> 0
    | AAAAAAAAAAAAAA, BBBB, _ -> 0
    | AAAAAAAAAAAAAAA, _, BBBB -> 0
    | _, AAAAAAAAAAAAAAAA, BBBB -> 0
    | AAAAAAAAAAAAAAAAA, BBBB, _ -> 0
    | AAAAAAAAAAAAAAAAAA, _, BBBB -> 0
    | _, AAAAAAAAAAAAAAAAAAA, BBBB -> 0
    | AAAAAAAAAAAAAAAAAAAA, BBBB, _ -> 0

    | B, _, BBBB -> 0
    | _, BB, BBBB -> 0
    | BBB, BBBB, _ -> 0
    | BBBB, _, BBBB -> 0
    | _, BBBBB, BBBB -> 0
    | BBBBBB, BBBB, _ -> 0
    | BBBBBBB, _, BBBB -> 0
    | _, BBBBBBBB, BBBB -> 0
    | BBBBBBBBB, BBBB, _ -> 0
    | BBBBBBBBBB, _, BBBB -> 0
    | _, BBBBBBBBBBB, BBBB -> 0
    | BBBBBBBBBBBB, BBBB, _ -> 0
    | BBBBBBBBBBBBB, _, BBBB -> 0
    | _, BBBBBBBBBBBBBB, BBBB -> 0
    | BBBBBBBBBBBBBBB, BBBB, _ -> 0
    | BBBBBBBBBBBBBBBB, _, BBBB -> 0
    | _, BBBBBBBBBBBBBBBBB, BBBB -> 0
    | BBBBBBBBBBBBBBBBBB, BBBB, _ -> 0
    | BBBBBBBBBBBBBBBBBBB, _, BBBB -> 0
    | _, BBBBBBBBBBBBBBBBBBBB, BBBB -> 0

    | A, BBBBB, _ -> 0
    | AA, _, BBBBB -> 0
    | _, AAA, BBBBB -> 0
    | AAAA, BBBBB, _ -> 0
    | AAAAA, _, BBBBB -> 0
    | _, AAAAAA, BBBBB -> 0
    | AAAAAAA, BBBBB, _ -> 0
    | AAAAAAAA, _, BBBBB -> 0
    | _, AAAAAAAAA, BBBBB -> 0
    | AAAAAAAAAA, BBBBB, _ -> 0
    | AAAAAAAAAAA, _, BBBBB -> 0
    | _, AAAAAAAAAAAA, BBBBB -> 0
    | AAAAAAAAAAAAA, BBBBB, _ -> 0
    | AAAAAAAAAAAAAA, _, BBBBB -> 0
    | _, AAAAAAAAAAAAAAA, BBBBB -> 0
    | AAAAAAAAAAAAAAAA, BBBBB, _ -> 0
    | AAAAAAAAAAAAAAAAA, _, BBBBB -> 0
    | _, AAAAAAAAAAAAAAAAAA, BBBBB -> 0
    | AAAAAAAAAAAAAAAAAAA, BBBBB, _ -> 0
    | AAAAAAAAAAAAAAAAAAAA, _, BBBBB -> 0

    | _, B, BBBBB -> 0
    | BB, BBBBB, _ -> 0
    | BBB, _, BBBBB -> 0
    | _, BBBB, BBBBB -> 0
    | BBBBB, BBBBB, _ -> 0
    | BBBBBB, _, BBBBB -> 0
    | _, BBBBBBB, BBBBB -> 0
    | BBBBBBBB, BBBBB, _ -> 0
    | BBBBBBBBB, _, BBBBB -> 0
    | _, BBBBBBBBBB, BBBBB -> 0
    | BBBBBBBBBBB, BBBBB, _ -> 0
    | BBBBBBBBBBBB, _, BBBBB -> 0
    | _, BBBBBBBBBBBBB, BBBBB -> 0
    | BBBBBBBBBBBBBB, BBBBB, _ -> 0
    | BBBBBBBBBBBBBBB, _, BBBBB -> 0
    | _, BBBBBBBBBBBBBBBB, BBBBB -> 0
    | BBBBBBBBBBBBBBBBB, BBBBB, _ -> 0
    | BBBBBBBBBBBBBBBBBB, _, BBBBB -> 0
    | _, BBBBBBBBBBBBBBBBBBB, BBBBB -> 0
    | BBBBBBBBBBBBBBBBBBBB, BBBBB, _ -> 0

    | A, _, BBBBBB -> 0
    | _, AA, BBBBBB -> 0
    | AAA, BBBBBB, _ -> 0
    | AAAA, _, BBBBBB -> 0
    | _, AAAAA, BBBBBB -> 0
    | AAAAAA, BBBBBB, _ -> 0
    | AAAAAAA, _, BBBBBB -> 0
    | _, AAAAAAAA, BBBBBB -> 0
    | AAAAAAAAA, BBBBBB, _ -> 0
    | AAAAAAAAAA, _, BBBBBB -> 0
    | _, AAAAAAAAAAA, BBBBBB -> 0
    | AAAAAAAAAAAA, BBBBBB, _ -> 0
    | AAAAAAAAAAAAA, _, BBBBBB -> 0
    | _, AAAAAAAAAAAAAA, BBBBBB -> 0
    | AAAAAAAAAAAAAAA, BBBBBB, _ -> 0
    | AAAAAAAAAAAAAAAA, _, BBBBBB -> 0
    | _, AAAAAAAAAAAAAAAAA, BBBBBB -> 0
    | AAAAAAAAAAAAAAAAAA, BBBBBB, _ -> 0
    | AAAAAAAAAAAAAAAAAAA, _, BBBBBB -> 0
    | _, AAAAAAAAAAAAAAAAAAAA, BBBBBB -> 0

    | B, BBBBBB, _ -> 0
    | BB, _, BBBBBB -> 0
    | _, BBB, BBBBBB -> 0
    | BBBB, BBBBBB, _ -> 0
    | BBBBB, _, BBBBBB -> 0
    | _, BBBBBB, BBBBBB -> 0
    | BBBBBBB, BBBBBB, _ -> 0
    | BBBBBBBB, _, BBBBBB -> 0
    | _, BBBBBBBBB, BBBBBB -> 0
    | BBBBBBBBBB, BBBBBB, _ -> 0
    | BBBBBBBBBBB, _, BBBBBB -> 0
    | _, BBBBBBBBBBBB, BBBBBB -> 0
    | BBBBBBBBBBBBB, BBBBBB, _ -> 0
    | BBBBBBBBBBBBBB, _, BBBBBB -> 0
    | _, BBBBBBBBBBBBBBB, BBBBBB -> 0
    | BBBBBBBBBBBBBBBB, BBBBBB, _ -> 0
    | BBBBBBBBBBBBBBBBB, _, BBBBBB -> 0
    | _, BBBBBBBBBBBBBBBBBB, BBBBBB -> 0
    | BBBBBBBBBBBBBBBBBBB, BBBBBB, _ -> 0
    | BBBBBBBBBBBBBBBBBBBB, _, BBBBBB -> 0

    | _, A, BBBBBBB -> 0
    | AA, BBBBBBB, _ -> 0
    | AAA, _, BBBBBBB -> 0
    | _, AAAA, BBBBBBB -> 0
    | AAAAA, BBBBBBB, _ -> 0
    | AAAAAA, _, BBBBBBB -> 0
    | _, AAAAAAA, BBBBBBB -> 0
    | AAAAAAAA, BBBBBBB, _ -> 0
    | AAAAAAAAA, _, BBBBBBB -> 0
    | _, AAAAAAAAAA, BBBBBBB -> 0
    | AAAAAAAAAAA, BBBBBBB, _ -> 0
    | AAAAAAAAAAAA, _, BBBBBBB -> 0
    | _, AAAAAAAAAAAAA, BBBBBBB -> 0
    | AAAAAAAAAAAAAA, BBBBBBB, _ -> 0
    | AAAAAAAAAAAAAAA, _, BBBBBBB -> 0
    | _, AAAAAAAAAAAAAAAA, BBBBBBB -> 0
    | AAAAAAAAAAAAAAAAA, BBBBBBB, _ -> 0
    | AAAAAAAAAAAAAAAAAA, _, BBBBBBB -> 0
    | _, AAAAAAAAAAAAAAAAAAA, BBBBBBB -> 0
    | AAAAAAAAAAAAAAAAAAAA, BBBBBBB, _ -> 0

    | B, _, BBBBBBB -> 0
    | _, BB, BBBBBBB -> 0
    | BBB, BBBBBBB, _ -> 0
    | BBBB, _, BBBBBBB -> 0
    | _, BBBBB, BBBBBBB -> 0
    | BBBBBB, BBBBBBB, _ -> 0
    | BBBBBBB, _, BBBBBBB -> 0
    | _, BBBBBBBB, BBBBBBB -> 0
    | BBBBBBBBB, BBBBBBB, _ -> 0
    | BBBBBBBBBB, _, BBBBBBB -> 0
    | _, BBBBBBBBBBB, BBBBBBB -> 0
    | BBBBBBBBBBBB, BBBBBBB, _ -> 0
    | BBBBBBBBBBBBB, _, BBBBBBB -> 0
    | _, BBBBBBBBBBBBBB, BBBBBBB -> 0
    | BBBBBBBBBBBBBBB, BBBBBBB, _ -> 0
    | BBBBBBBBBBBBBBBB, _, BBBBBBB -> 0
    | _, BBBBBBBBBBBBBBBBB, BBBBBBB -> 0
    | BBBBBBBBBBBBBBBBBB, BBBBBBB, _ -> 0
    | BBBBBBBBBBBBBBBBBBB, _, BBBBBBB -> 0
    | _, BBBBBBBBBBBBBBBBBBBB, BBBBBBB -> 0

    | A, BBBBBBBB, _ -> 0
    | AA, _, BBBBBBBB -> 0
    | _, AAA, BBBBBBBB -> 0
    | AAAA, BBBBBBBB, _ -> 0
    | AAAAA, _, BBBBBBBB -> 0
    | _, AAAAAA, BBBBBBBB -> 0
    | AAAAAAA, BBBBBBBB, _ -> 0
    | AAAAAAAA, _, BBBBBBBB -> 0
    | _, AAAAAAAAA, BBBBBBBB -> 0
    | AAAAAAAAAA, BBBBBBBB, _ -> 0
    | AAAAAAAAAAA, _, BBBBBBBB -> 0
    | _, AAAAAAAAAAAA, BBBBBBBB -> 0
    | AAAAAAAAAAAAA, BBBBBBBB, _ -> 0
    | AAAAAAAAAAAAAA, _, BBBBBBBB -> 0
    | _, AAAAAAAAAAAAAAA, BBBBBBBB -> 0
    | AAAAAAAAAAAAAAAA, BBBBBBBB, _ -> 0
    | AAAAAAAAAAAAAAAAA, _, BBBBBBBB -> 0
    | _, AAAAAAAAAAAAAAAAAA, BBBBBBBB -> 0
    | AAAAAAAAAAAAAAAAAAA, BBBBBBBB, _ -> 0
    | AAAAAAAAAAAAAAAAAAAA, _, BBBBBBBB -> 0

    | _, B, BBBBBBBB -> 0
    | BB, BBBBBBBB, _ -> 0
    | BBB, _, BBBBBBBB -> 0
    | _, BBBB, BBBBBBBB -> 0
    | BBBBB, BBBBBBBB, _ -> 0
    | BBBBBB, _, BBBBBBBB -> 0
    | _, BBBBBBB, BBBBBBBB -> 0
    | BBBBBBBB, BBBBBBBB, _ -> 0
    | BBBBBBBBB, _, BBBBBBBB -> 0
    | _, BBBBBBBBBB, BBBBBBBB -> 0
    | BBBBBBBBBBB, BBBBBBBB, _ -> 0
    | BBBBBBBBBBBB, _, BBBBBBBB -> 0
    | _, BBBBBBBBBBBBB, BBBBBBBB -> 0
    | BBBBBBBBBBBBBB, BBBBBBBB, _ -> 0
    | BBBBBBBBBBBBBBB, _, BBBBBBBB -> 0
    | _, BBBBBBBBBBBBBBBB, BBBBBBBB -> 0
    | BBBBBBBBBBBBBBBBB, BBBBBBBB, _ -> 0
    | BBBBBBBBBBBBBBBBBB, _, BBBBBBBB -> 0
    | _, BBBBBBBBBBBBBBBBBBB, BBBBBBBB -> 0
    | BBBBBBBBBBBBBBBBBBBB, BBBBBBBB, _ -> 0
    | _, _, _ -> 1

end

