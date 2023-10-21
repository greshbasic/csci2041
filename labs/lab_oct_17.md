# Code definitions:

```ocaml
let ( >>= ) o f =
    match o with
    | None -> None
    | Some y -> f y

let return x = Some x
```

# Example Proof:

```
Prove:
	x >>= return = x, for (x: 'a option)

By cases on (x: 'a option):

Case x = None:

	x >>= return
= { case }
	None >>= return
= { bind def }
	match None with
	| None -> None
	| Some a -> return a
= { apply match }
	None
= { case }
	x

Case x = Some y:

	x >>= return
= { case }
	Some y >>= return
= { bind def }
	match Some y with
	| None -> None
	| Some a -> return a
= { apply match }
	return a
= { return def }
	Some a
= { case }
	x

We have proven the statement for all possible values of x, so the statement is true, namely x >>= return = x for any (x: 'a option)
```

# Problem 1

```
Prove:
	(x >>= g) >>= h = x >>= (fun y -> g y >>= h), for (x: 'a option)

By cases on (x: 'a option):

Case x = None

	(x >>= g) >>= h
= { case }
	(None >>= g) >>= h
= { bind def }
	match None with
	| None -> None
	| Some a -> g a
= { apply match }
	(None) >>= h
= { bind def }
	match None with
	| None -> None
	| Some a -> h a
= { apply match }
	None
= { case }
	x

	x >>= (fun y -> g y >>= h)
= { case }
	None >>= (fun y -> g y >>= h)
= { bind def }
	match None with
	| None -> None
	| Some a -> y a
= { apply match }
	None
= { case }
	x


Case x = Some z

	(x >>= g) >>= h
= { case }
	(Some z >>= g) >>= h
= { bind def }
	match Some z with
	| None -> None
	| Some a -> g a
= { apply match }
	(g z) >>= h
= { bind def }
	match (g z)with
	| None -> None
	| Some a -> h a
= { apply match }
	h (g z)

	x >>= (fun y -> g y >>= h)
= { case }
	Some z >>= (fun y -> g y >>= h)
= { bind def }
	match Some z with
	| None -> None
	| Some a -> (fun y -> g y >>= h) a
= { apply match }
	(fun y -> g y >>= h) z
= { fun def }
	g z >>= h
= { bind def }
	match (g z) with
	| None -> None
	| Some a -> h a
= { apply match }
	h (g z)
-------------------------------------------------

It is shown that for all possible values of X, return (x >>= g) >>= h and x >>= (fun y -> g y >>= h) are equivalent, thus we have proven the statement true for any (x: 'a option)


```

# Problem 2

```
Prove:
	return x >>= f = f x, for (x: 'a option)

By cases on (x: 'a option):

Case x = None:

---- return x >>= f when x = None ----
	return x >>= f
= { case }
	return None >>= f
= { return def }
	Some None >>= f
= { bind def }
	match Some None with
	| None -> None
	| Some a -> f a
= { apply match }
	f None
= { case }
	f x

---- f x when x = None ----
	f x
= { case }
	f None
= { case }
	f x
-------------------------------------------------
---- return x >>= f when x = Some y ----
Case x = Some y:

	return x >>= f
= { case }
	return Some y >>= f
= { return def }
	Some (Some y) >>= f
= { bind def }
	match Some (Some y) with
	| None -> None
	| Some a -> f a
= { apply match }
	f (Some y)
= { case }
	f x

---- f x when x = Some y ----
	f x
= { case }
	f Some y
= { case }
	f x

It is shown that for all possible values of X, return x >>= f and f x are equivalent, thus we have proven the statement true for any (x: 'a option)

```

# Problem 3

```
Prove:
	x >>= (fun x' -> y >>= (fun y' -> plus x' y')) =
		match y with 
		| None -> None
		| Some y' -> (
			match x with 
			| None -> None
			| Some x' -> plus x' y')

```
By cases on (x: 'a option):

----Case x = None, y = None----
	x >>= (fun x' -> y >>= (fun y' -> plus x' y'))
= { case }
	None >>= (fun x' -> y >>= (fun y' -> plus x' y'))
= { bind def }
	match None with
	| None -> None
	| Some a -> fun a
= { apply match }
	None
= { case }
	x

	match y with 
	| None -> None
	| Some y' -> (
		match x with 
		| None -> None
		| Some x' -> plus x' y')
= { case }
	match None with 
	| None -> None
	| Some y' -> (
		match x with 
		| None -> None
		| Some x' -> plus x' y')
 = { apply match }
	None
= { case }
	x

 ----Case x = Some a, y = None----
	x >>= (fun x' -> y >>= (fun y' -> plus x' y'))
= { case }
	Some z >>= (fun x' -> y >>= (fun y' -> plus x' y'))
= { bind def }
	match Some z with
	| None -> None
	| Some a -> fun a
= { apply match }
	fun z >>= (fun y' -> plus x' y')
= { fun def }
	y >>= (fun y' -> plus x' y')
= { bind def }
	match Some None with
	| None -> None
	| Some a -> plus x' None
= { apply match }
	plus a None
= { case }
	plus x None
= { eval }
	None
= { case }
	y

	match y with 
	| None -> None
	| Some y' -> (
		match x with 
		| None -> None
		| Some x' -> plus x' y')
= { case }
	match None with 
	| None -> None
	| Some y' -> (
		match Some a with 
		| None -> None
		| Some x' -> plus x' y')
= { apply match }
	None
= { case }
	y

----Case x = None, y = Some b----
	x >>= (fun x' -> y >>= (fun y' -> plus x' y'))
= { case }
	None >>= (fun x' -> y >>= (fun y' -> plus x' y'))
= { bind def }
	match None with
	| None -> None
	| Some a -> fun a
= { apply match }
	None
= { case }
	x

match y with 
	| None -> None
	| Some y' -> (
		match x with 
		| None -> None
		| Some x' -> plus x' y')
= { case }
	match Some b with
	| None -> None
	| Some y' -> (
		match x with 
		| None -> None
		| Some x' -> plus x' y')
= { apply match }
	match None with 
	| None -> None
	| Some x' -> plus x' y'
= { apply match }
	None
= { case }
	x

----Case x = Some a, y = Some b----
	x >>= (fun x' -> y >>= (fun y' -> plus x' y'))
= { case }
	Some a >>= (fun x' -> y >>= (fun y' -> plus x' y'))
= { bind def }
	match Some a with
	| None -> None
	| Some a -> (fun a -> y >>= (fun y' -> plus x' y'))
= { apply match }
	fun a -> y >>= (fun y' -> plus Some a y')
= { fun def }
	y >>= (fun y' -> plus Some a y')
= { case }
	Some b >>= (fun y' -> plus Some a y')
= { bind def }
	match Some b with
	| None -> None
	| Some a -> (fun y' -> plus Some a y')
= { apply match }
	fun b -> plus Some a Some b
= { fun def }
	plus Some a Some b
= { eval }
	Some a + Some b
= { case }
	x + y


match y with 
	| None -> None
	| Some y' -> (
		match x with 
		| None -> None
		| Some x' -> plus x' y')
= { case }
	match Some b with
	| None -> None
	| Some y' -> (
		match x with 
		| None -> None
		| Some x' -> plus x' y')
= { apply match }
	match Some a with 
	| None -> None
	| Some x' -> plus x Some b
= { apply match }
	plus Some a Some b
= { eval }
	Some a + Some b
= { case }
	x + y


It is shown that for all possible values of X, both methods provide the same results, thus we have proven the statement true for any (x: 'a option)









	

