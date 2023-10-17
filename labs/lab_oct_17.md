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
	| Some a -> fun a
= { apply match }
	fun z
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
	None >>= f
= { bind def }
	match None with
	| None -> None
	| Some a -> f a
= { apply match }
	None
= { case }
	x

---- f x when x = None ----
	f x
= { case }
	f None
= { bind def }
	match None with
	| None -> None
	| Some a -> f a
= { apply match }
	None
= { case }
	x
-------------------------------------------------
---- return x >>= f when x = Some y ----
Case x = Some y:

	return x >>= f
= { case }
	return Some y >>= f
= { return def }
	Some y >>= f
= { bind def }
	match Some y with
	| None -> None
	| Some a -> f a
= { apply match }
	f y
= { case }
	f x

---- f x when x = Some y ----
	f x
= { case }
	f Some y
= { bind def }
	match Some y with
	| None -> None
	| Some a -> f a
= { apply match }
	f y
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

Case x = None:
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
 

 Case x = Some z
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
	match Some y with
	| None -> None
	| Some a -> fun y
= { apply match }
	fun y
= { fun def }
	plus z y
= { case }
	plus x y
= { eval }
	x + y



	

