// json2dir evaluator in BCPL (Martin Richards' Cintcode system).
// Usage inside cintsys: json2dir IN OUT
// Reads the document from the file IN byte by byte, checks strict UTF-8,
// parses and validates the whole JSON document by hand, then writes a
// POSIX sh script to the file OUT. The last line of a complete script is
// the marker "# json2dir: end". Errors go to stderr with returncode 20.
// Bytes are kept one per word in vectors from GETVEC.

GET "libhdr"

GLOBAL {
  inb: ug         // input bytes
  n; pos
  pool; pooln     // decoded string bytes
  str_s; str_l    // last parsed string (offset/length in pool)
  // nodes: kind 0 object, 1 file, 2 link, 3 script
  nkind; nstart; nlen; nmfirst; nmcount; nn
  // members: name (pool offset/length) and value node
  mname_s; mname_l; mval; mn
  objmem; objn    // member indices of each object, contiguous, sorted by name
  pend; pendn     // stack of members of the objects being parsed
  path; pathn     // path bytes while emitting
}

MANIFEST { maxdepth = 1000 }

LET fail(msg) BE
{ errwritef("json2dir: %s*n", msg)
  stop(20, 0)
}

AND newvec(upb) = VALOF
{ LET v = getvec(upb)
  UNLESS v DO fail("out of memory")
  RESULTIS v
}

AND peek() = pos < n -> inb!pos, -1

AND skip_ws() BE
  WHILE pos < n & (inb!pos = 32 | inb!pos = 9 | inb!pos = 10 | inb!pos = 13) DO
    pos := pos + 1

AND check_utf8() BE
{ LET i = 0
  WHILE i < n DO
  { LET b = inb!i
    LET need, lo, hi = 0, #x80, #xBF
    TEST b < #x80 THEN need := 0
    ELSE TEST #xC2 <= b <= #xDF THEN need := 1
    ELSE TEST b = #xE0 THEN { need := 2; lo := #xA0 }
    ELSE TEST #xE1 <= b <= #xEC THEN need := 2
    ELSE TEST b = #xED THEN { need := 2; hi := #x9F }
    ELSE TEST #xEE <= b <= #xEF THEN need := 2
    ELSE TEST b = #xF0 THEN { need := 3; lo := #x90 }
    ELSE TEST #xF1 <= b <= #xF3 THEN need := 3
    ELSE TEST b = #xF4 THEN { need := 3; hi := #x8F }
    ELSE fail("input is not valid UTF-8")
    i := i + 1
    FOR k = 1 TO need DO
    { IF i >= n | inb!i < lo | inb!i > hi DO fail("input is not valid UTF-8")
      lo, hi := #x80, #xBF
      i := i + 1
    }
  }
}

AND put(b) BE { pool!pooln := b; pooln := pooln + 1 }

AND put_cp(cp) BE
  TEST cp < #x80 THEN put(cp)
  ELSE TEST cp < #x800 THEN
  { put(#xC0 | cp >> 6); put(#x80 | cp & #x3F) }
  ELSE TEST cp < #x10000 THEN
  { put(#xE0 | cp >> 12); put(#x80 | (cp >> 6) & #x3F); put(#x80 | cp & #x3F) }
  ELSE
  { put(#xF0 | cp >> 18); put(#x80 | (cp >> 12) & #x3F)
    put(#x80 | (cp >> 6) & #x3F); put(#x80 | cp & #x3F)
  }

AND hexval(c) = '0' <= c <= '9' -> c - '0',
                'a' <= c <= 'f' -> c - 'a' + 10,
                'A' <= c <= 'F' -> c - 'A' + 10,
                -1

AND hex4() = VALOF
{ LET v = 0
  FOR k = 1 TO 4 DO
  { LET h = hexval(peek())
    IF h < 0 DO fail("invalid \u escape")
    v := v * 16 + h
    pos := pos + 1
  }
  RESULTIS v
}

// Parses a JSON string at pos (which must be '"') into the pool.
AND parse_string() BE
{ IF peek() ~= '"' DO fail("expected a string")
  pos := pos + 1
  str_s := pooln
  { LET c = peek()
    IF c < 0 DO fail("unterminated string")
    pos := pos + 1
    IF c = '"' BREAK
    IF c < 32 DO fail("control character in string")
    TEST c ~= '\' THEN put(c)
    ELSE
    { c := peek()
      pos := pos + 1
      SWITCHON c INTO
      { DEFAULT:  fail("invalid escape in string")
        CASE '"': put('"');  ENDCASE
        CASE '\': put('\');  ENDCASE
        CASE '/': put('/');  ENDCASE
        CASE 'b': put(8);    ENDCASE
        CASE 'f': put(12);   ENDCASE
        CASE 'n': put(10);   ENDCASE
        CASE 'r': put(13);   ENDCASE
        CASE 't': put(9);    ENDCASE
        CASE 'u':
        { LET cp = hex4()
          IF #xDC00 <= cp <= #xDFFF DO fail("unpaired surrogate escape")
          IF #xD800 <= cp <= #xDBFF DO
          { LET lo = 0
            IF peek() ~= '\' DO fail("unpaired surrogate escape")
            pos := pos + 1
            IF peek() ~= 'u' DO fail("unpaired surrogate escape")
            pos := pos + 1
            lo := hex4()
            UNLESS #xDC00 <= lo <= #xDFFF DO fail("unpaired surrogate escape")
            cp := #x10000 + ((cp - #xD800) << 10) + (lo - #xDC00)
          }
          put_cp(cp)
          ENDCASE
        }
      }
    }
  } REPEAT
  str_l := pooln - str_s
}

AND pool_has(s, l, b) = VALOF
{ FOR k = 0 TO l - 1 DO IF pool!(s + k) = b RESULTIS TRUE
  RESULTIS FALSE
}

// Is the pool slice equal to the BCPL string w?
AND pool_is(s, l, w) = VALOF
{ UNLESS l = w%0 RESULTIS FALSE
  FOR k = 0 TO l - 1 DO UNLESS pool!(s + k) = w%(k + 1) RESULTIS FALSE
  RESULTIS TRUE
}

// <0, 0, >0 comparing the names of two members by their UTF-8 bytes
AND name_cmp(a, b) = VALOF
{ LET la, lb = mname_l!a, mname_l!b
  LET k = 0
  WHILE k < la & k < lb DO
  { LET r = pool!(mname_s!a + k) - pool!(mname_s!b + k)
    IF r RESULTIS r
    k := k + 1
  }
  RESULTIS la - lb
}

AND new_node(kind, s, l) = VALOF
{ nkind!nn, nstart!nn, nlen!nn := kind, s, l
  nmfirst!nn, nmcount!nn := 0, 0
  nn := nn + 1
  RESULTIS nn - 1
}

AND parse_value(depth) = VALOF
{ LET c = 0
  IF depth > maxdepth DO fail("document is nested too deeply")
  skip_ws()
  c := peek()
  IF c = '"' DO
  { parse_string()
    RESULTIS new_node(1, str_s, str_l)
  }
  IF c = '[' DO
  { LET kind = 0
    pos := pos + 1
    skip_ws()
    parse_string()
    TEST pool_is(str_s, str_l, "link") THEN kind := 2
    ELSE TEST pool_is(str_s, str_l, "script") THEN kind := 3
    ELSE fail("an array must be [*"link*", target] or [*"script*", content]")
    skip_ws()
    IF peek() ~= ',' DO fail("an array must have exactly two strings")
    pos := pos + 1
    skip_ws()
    parse_string()
    skip_ws()
    IF peek() ~= ']' DO fail("an array must have exactly two strings")
    pos := pos + 1
    IF kind = 2 & pool_has(str_s, str_l, 0) DO fail("a link target cannot contain NUL")
    IF kind = 2 & str_l = 0 DO fail("a link target cannot be empty")
    RESULTIS new_node(kind, str_s, str_l)
  }
  IF c = '{' DO
  { LET base, node = pendn, 0
    pos := pos + 1
    skip_ws()
    TEST peek() = '}' THEN pos := pos + 1
    ELSE
    { LET ns, nl, v = 0, 0, 0
      skip_ws()
      parse_string()
      ns, nl := str_s, str_l
      IF nl = 0 DO fail("empty name")
      IF pool_is(ns, nl, ".") | pool_is(ns, nl, "..") DO fail("name . or .. is not allowed")
      IF pool_has(ns, nl, '/') DO fail("a name cannot contain /")
      IF pool_has(ns, nl, 0) DO fail("a name cannot contain NUL")
      skip_ws()
      IF peek() ~= ':' DO fail("expected :")
      pos := pos + 1
      v := parse_value(depth + 1)
      mname_s!mn, mname_l!mn, mval!mn := ns, nl, v
      pend!pendn := mn
      mn, pendn := mn + 1, pendn + 1
      skip_ws()
      c := peek()
      pos := pos + 1
      IF c = '}' BREAK
      IF c ~= ',' DO fail("expected , or }")
    } REPEAT
    // stable insertion sort of this object's members by name bytes
    FOR i = base + 1 TO pendn - 1 DO
    { LET t, j = pend!i, i - 1
      WHILE j >= base & name_cmp(pend!j, t) > 0 DO
      { pend!(j + 1) := pend!j
        j := j - 1
      }
      pend!(j + 1) := t
    }
    node := new_node(0, 0, 0)
    nmfirst!node, nmcount!node := objn, pendn - base
    FOR i = base TO pendn - 1 DO
    { objmem!objn := pend!i
      objn := objn + 1
    }
    pendn := base
    RESULTIS node
  }
  fail("only objects, strings and [kind, payload] arrays are allowed")
  RESULTIS 0
}

// single-quoted shell word; NUL bytes split the payload into separate words
AND put_quoted_pool(s, l) BE
{ wrch('*'')
  FOR k = 0 TO l - 1 DO
  { LET b = pool!(s + k)
    TEST b = 0 THEN writes("' '")
    ELSE TEST b = '*'' THEN writes("'\''")
    ELSE wrch(b)
  }
  wrch('*'')
}

AND put_path() BE
{ wrch('*'')
  FOR k = 0 TO pathn - 1 DO
  { LET b = path!k
    TEST b = '*'' THEN writes("'\''") ELSE wrch(b)
  }
  wrch('*'')
}

AND emit(node) BE
  FOR i = 0 TO nmcount!node - 1 DO
  { LET m = objmem!(nmfirst!node + i)
    // duplicate names: the last occurrence wins (the sort is stable)
    UNLESS i + 1 < nmcount!node & name_cmp(m, objmem!(nmfirst!node + i + 1)) = 0 DO
    { LET v, plen = mval!m, pathn
      IF plen > 0 DO { path!pathn := '/'; pathn := pathn + 1 }
      FOR k = 0 TO mname_l!m - 1 DO
      { path!pathn := pool!(mname_s!m + k)
        pathn := pathn + 1
      }
      SWITCHON nkind!v INTO
      { CASE 0: writes("_j2d_dir "); put_path(); wrch('*n')
                emit(v)
                ENDCASE
        CASE 1: writes("_j2d_file "); ENDCASE
        CASE 2: writes("_j2d_link "); ENDCASE
        CASE 3: writes("_j2d_script "); ENDCASE
      }
      UNLESS nkind!v = 0 DO
      { put_path(); wrch(' ')
        put_quoted_pool(nstart!v, nlen!v); wrch('*n')
      }
      pathn := plen
    }
  }

AND line(s) BE { writes(s); wrch('*n') }

AND write_helpers() BE
{ line("set -eu")
  line("_j2d_fail() { printf 'json2dir: cannot create %s\n' *"$1*" >&2; exit 1; }")
  line("# Remove an existing non-directory (a symlink itself, never its target);")
  line("# a real directory in the way of a non-object is an error.")
  line("_j2d_clear() {")
  line("  if [ -L *"$1*" ]; then rm -f -- *"$1*" || _j2d_fail *"$1*"")
  line("  elif [ -d *"$1*" ]; then printf 'json2dir: a directory is in the way: %s\n' *"$1*" >&2; exit 1")
  line("  elif [ -e *"$1*" ]; then rm -f -- *"$1*" || _j2d_fail *"$1*"")
  line("  fi")
  line("}")
  line("_j2d_dir() {")
  line("  if [ -L *"$1*" ] || { [ -e *"$1*" ] && [ ! -d *"$1*" ]; }; then rm -f -- *"$1*" || _j2d_fail *"$1*"; fi")
  line("  if [ ! -d *"$1*" ]; then mkdir -- *"$1*" || _j2d_fail *"$1*"; fi")
  line("}")
  line("# _j2d_file path part...: the content is the parts joined by NUL bytes.")
  line("_j2d_file() {")
  line("  _j2d_clear *"$1*"")
  line("  _j2d_path=$1; shift")
  line("  {")
  line("    printf '%s' *"$1*"; shift")
  line("    for _j2d_part in *"$@*"; do printf '\000%s' *"$_j2d_part*"; done")
  line("  } > *"$_j2d_path*" || _j2d_fail *"$_j2d_path*"")
  line("}")
  line("_j2d_script() { _j2d_file *"$@*"; chmod a+x -- *"$1*" || _j2d_fail *"$1*"; }")
  line("_j2d_link() { _j2d_clear *"$1*"; ln -s -- *"$2*" *"$1*" || _j2d_fail *"$1*"; }")
}

LET start() = VALOF
{ LET argv = VEC 100
  LET in, out, c, upb = 0, 0, 0, 0
  IF rdargs("IN/A,OUT/A", argv, 100) = 0 DO fail("usage: json2dir IN OUT")

  // first pass: count the bytes; second pass: keep them
  in := findinput(argv!0)
  UNLESS in DO fail("cannot open the input file")
  selectinput(in)
  n := 0
  UNTIL binrdch() = endstreamch DO n := n + 1
  endread()
  upb := n + 16
  inb := newvec(upb)
  in := findinput(argv!0)
  UNLESS in DO fail("cannot open the input file")
  selectinput(in)
  FOR i = 0 TO n - 1 DO inb!i := binrdch()
  endread()

  pool, pooln := newvec(upb), 0
  nkind, nstart, nlen := newvec(upb), newvec(upb), newvec(upb)
  nmfirst, nmcount, nn := newvec(upb), newvec(upb), 0
  mname_s, mname_l, mval, mn := newvec(upb), newvec(upb), newvec(upb), 0
  objmem, objn := newvec(upb), 0
  pend, pendn := newvec(upb), 0
  path, pathn := newvec(upb), 0

  check_utf8()
  pos := 0
  // a leading byte order mark is ignored (RFC 8259 permits it)
  IF n >= 3 & inb!0 = #xEF & inb!1 = #xBB & inb!2 = #xBF DO pos := 3
  skip_ws()
  IF peek() ~= '{' DO fail("the root of the document must be an object")
  c := parse_value(0)
  skip_ws()
  IF pos < n DO fail("trailing data after the JSON value")

  out := findoutput(argv!1)
  UNLESS out DO fail("cannot open the output file")
  selectoutput(out)
  write_helpers()
  emit(c)
  line("# json2dir: end")
  endwrite()
  RESULTIS 0
}
