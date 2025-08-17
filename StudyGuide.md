Here’s the **Type Space & Modes** add-on for Phoenix ProLang, answering “is it strong/explicit/dynamic,” and slotting cleanly into the spec.

# Type Space & Modes

## 1) Posture at a glance

* **Strength:** **Strongly typed.** No silent coercions; all conversions are explicit or rule-driven via validators/traits.
* **Timing:** **Statically typed by default** with **local type inference** (Hindley–Milner–style inference constrained by Phoenix traits/validators).
* **Dynamism:** **Gradual typing lane available** via `dynamic`/`any`/`reflect` with validator guards. Dynamic regions are opt-in and sandboxed.
* **Nullability:** **Non-nullable by default.** `null` is only legal for pointer-like and `option<T>`; otherwise use `option<T>` or `nullable<T>`.
* **Ownership:** Linear/affine semantics through `lease/sublease/release` with **lifetime inference** (no lifetime annotations in the surface syntax).

---

## 2) The Phoenix Type Space

### 2.1 Primitives

```
bool, byte, u16, u32, u64, i16, i32, i64, f32, f64, char, codepoint,
duration, index, size, checksum
```

* `bool` is 1-byte, truthy only if `true`.
* `duration` carries unit metadata (ns/µs/ms/s) at type level; arithmetic requires unit compatibility or explicit cast.
* `index`, `size` are platform-wide unsigned types (bounds-checked in validators when enabled).

### 2.2 Aggregates & algebraic types

* **Tuples:** `(T1, T2, …)`
* **Records/classes:** `class Point { x:i32; y:i32; }`
* **Arrays/packets:** `packet<T>[N]` (layout + alignment guaranteed)
* **Sum types / enums with data:**

  ```phoenix
  enum Result<T,E> { Ok(T), Err(E) }
  ```
* **Optionals:** `option<T>` (preferred over raw nullables)

### 2.3 Reference & pointer space

* **References:** `ref T` (non-owning, non-nullable)
* **Pointers:** `ptr T` (owning semantics via `lease`), can be `null`
* **Smart handles:** `smart<T>`, `unique<T>`, `shared<T>` (policies selectable)
* **Slices/views:** `view<T>` (fat pointer: ptr + length; no ownership)

### 2.4 Traits / Validators (typeclass-like)

* Constraints live as **traits** (compile-time) and **validators** (prove/run-time).

  * Examples: `Sized`, `Send`, `Sync`, `Aligned<N>`, `Checksum`.

  ```phoenix
  fn sum<T: Add + Zero>(xs: view<T>) -> T { ... }
  ```

### 2.5 Generics

* **Parametric polymorphism** with trait bounds:

  ```phoenix
  class Box<T: Sized + Send> { inner: T }
  fn swap<T>(a: ref T, b: ref T) { ... }
  ```

### 2.6 Effects & safety capsules

* **Capsules** annotate blocks with safety guarantees (no data races, bounds proven, etc.). These are **not** types but constrain the type checker’s allowed moves within a region.

---

## 3) Modes: Explicit, Inferred, Dynamic

### 3.1 Explicit typing (always available)

```phoenix
let n: i32 = 42;
let v: packet<f64>[1024] = aloc<packet<f64>[1024]>();
```

### 3.2 Local type inference (default ergonomic mode)

* `let` allows **inference** from the initializer:

  ```phoenix
  let z = 3.14;      // z: f64
  let p = Point{ x:1, y:2 }; // p: Point
  ```
* Inference is **local and deterministic**; no global backtracking.
* Overloads resolve only with sufficient type evidence; ambiguous calls require an **ascription**:

  ```phoenix
  let s = parse("5") : Result<i32, ParseErr>;
  ```

### 3.3 Gradual/dynamic typing (opt-in, fenced)

* **`dynamic`** holds any runtime value with a vtable-like tag; **`any`** is a compile-time erased carrier that becomes `dynamic` at boundaries.
* All dynamic use must go through **validator/trait checks** or **pattern matches**:

  ```phoenix
  let d: dynamic = json::parse(src);
  match d {
    as i: i64      => print(i+1),
    as s: string   => print(len(s)),
    _              => deny "unexpected type"
  }
  ```
* Crossing into `dynamic` **never** leaks into static regions without an explicit check/cast:

  ```phoenix
  let x: i32 = assume<int>(d) where validator is_i32(d);
  ```

---

## 4) Conversions & Coercions

### 4.1 Implicit (limited, safe, lossless only)

* `i32 → i64`, `f32 → f64`, `&T → view<T>` (when size known), `option<T> → option<U>` if `T→U` is implicit.
* **No** numeric narrowing, **no** bool↔int, **no** float→int implicit.

### 4.2 Explicit (spelled by you)

* `cast<T>(expr)` or postfix `: T` ascription:

  ```phoenix
  let x = cast<i16>(some_i64);
  let y = (3.0): f32;
  ```

### 4.3 Validator-mediated casts

* Require a named proof:

  ```phoenix
  let idx: index = cast_if<index>(n) where validator nonneg(n);
  ```

---

## 5) Nullability & Option Discipline

* Default fields/refs are **non-nullable**. To allow “absent,” use:

  * `option<T>` and match:

    ```phoenix
    let maybe: option<string> = none;
    match maybe { some(s) => print(s), none => print("empty") }
    ```
  * Or `nullable<T>` for interop, with stricter checks than `option<T>`.

---

## 6) Ownership, Lifetimes, and Aliasing

### 6.1 Lease/sublease (linear/affine core)

* `lease` creates **exclusive** ownership with a statically bounded lifetime (inferred to the block).
* `sublease` creates **shared, read-only** borrows with non-overlapping mutation.
* The compiler performs **lifetime inference** and **borrow checking**; no annotations needed in surface code.

```phoenix
lease buf = aloc<packet<byte>[1024]>();
{
  sublease head = buf[0..64];   // read view
  // write(buf) is illegal while `head` is alive unless proven disjoint
}
release buf;
```

### 6.2 Mutation gates

* Mutation of a leased object while any sublease exists is rejected unless:

  * The write is to a **proven disjoint** range (using range validators), or
  * All subleases are out of scope.

---

## 7) Overloading, Traits, and Inference

* Operator overloading is **trait-driven** (e.g., `Add`, `Mul`, `Eq`, `Ord`).
* Method resolution prefers **inherent impls**, then **trait impls** in scope.
* Inference picks the **most specific** candidate; ties require ascription.

```phoenix
trait Add<Rhs, Out> { fn add(self, rhs:Rhs) -> Out }
impl Add<i32,i32> for i32 { ... }
```

---

## 8) Compile-time Evaluation & Const

* `@consteval` functions evaluate at compile time; results are **typed constants**.
* `const` values participate in type-level arithmetic for sizes/alignments:

  ```phoenix
  const N: size = 1024;
  let b: packet<byte>[N];
  ```

---

## 9) Reflection & `typeof`

* `typeof(expr)` yields a fully resolved static type.
* `reflect<T>` exposes metadata (size, align, fields, traits satisfied) for **build-time macros**; not available at runtime unless `dynamic`.

---

## 10) Error Types & Exceptions

* Checked error algebra via `Result<T,E>` is preferred.
* `throw`/`try`/`catch` exist but **must declare** thrown types:

  ```phoenix
  fn risky() throws IoError { ... }
  try { risky(); } catch (e: IoError) { ... }
  ```
* The type system enforces catch coverage for declared throws.

---

## 11) EBNF snippets (types & binds)

```
Type        := SimpleType
            | Type "[" Expr "]"         // arrays/packets
            | "option" "<" Type ">"
            | "nullable" "<" Type ">"
            | "view" "<" Type ">"
            | "ptr"  "<" Type ">"
            | "ref"  "<" Type ">"
            | "(" Type ("," Type)+ ")"  // tuple
            | Ident "<" TypeList ">"    // generic

Binder      := ("let" | "lease" | "sublease") Ident (":" Type)? ("=" Expr)?
Ascription  := Expr ":" Type
Cast        := "cast" "<" Type ">" "(" Expr ")"
```

---

## 12) Quick contrasts (for clarity)

* **Strong vs Weak:** Phoenix is **strong**—no silent lossy conversions; validators gate risky moves.
* **Static vs Dynamic:** **Static by default** with **gradual dynamic pockets** (`dynamic`/`any`) behind explicit fences.
* **Explicit vs Inferred:** Both. Types are **explicit when you want**, **inferred when obvious**; ambiguity must be resolved by you.

---

## 13) Micro-examples

**Explicit & inferred mix**

```phoenix
let a = 1;              // i32
let b: i64 = a;         // explicit widening OK
let c: f32 = cast<f32>(b);
```

**Dynamic pocket with guard**

```phoenix
let d: dynamic = get_config();
if (is<int>(d)) {
  let n: i32 = assume<int>(d);
  print(n+1);
} else deny "config must be int";
```

**Ownership and options**

```phoenix
lease file = File("out.txt");           // wrapper + lease
let maybe_line: option<string> = file.read_line();
match maybe_line { some(s) => print(s), none => () }
release file;
```

---

