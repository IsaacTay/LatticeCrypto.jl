using Random
using Base.Iterators

import Base.rand

using AbstractAlgebra
using Primes
using ProgressMeter

abstract type NTRU end

struct Params{NTRU}
	N::Int
	p::Int
	q::Int
	d::Int
	function Params{NTRU}(; N = 67, p = 257, q = 18773, d = 12)
		if !isprime(N)
			return error("N needs to be prime")
		elseif !isprime(p)
			return error("p needs to be prime")
		elseif gcd(p, q) !== 1
			return error("Failed gcd(p, q) = 1 check")
		elseif gcd(N, q) !== 1
			return error("Failed gcd(N, q) = 1 check")
		# elseif q <= (6d + 1)p
		# 	return error("Failed q > (6d + 1)p check")
		end
		return new{NTRU}(N, p, q, d)
	end
end

struct Private_Key{NTRU}
	params::Params{NTRU}
	f
	Fp
end

struct Public_Key{NTRU}
	params::Params{NTRU}
	key
end

function rand_NTRU(N_min, N_max, p_min, p_max, q_min, q_max, d_min, d_max)
	N = rand(primes(N_min, N_max))
	p = rand(primes(p_min, p_max))
	q = rand(primes(q_min, q_max))
	d = rand(d_min:d_max)
	return Params{NTRU}(; N, p, q, d)
end

function rand(p::Params{NTRU})
	prog = ProgressUnknown("Private Keys Tried: ");
	while true
		f = T(p.d, p.d+1, p.N)
		Fp = Fq = Nothing
		try
			Fq = inv(ringify(f, p.q, p.N))
			Fp = inv(ringify(f, p.p, p.N))
		catch e
			if isa(e, NotInvertibleError)
				next!(prog; showvalues=[(:error, repr(e))])
				continue
			else
				throw(e)
			end
		end
		g = ringify(T(p.d, p.d, p.N), p.q, p.N);
		return Private_Key{NTRU}(p, f, Fp), Public_Key{NTRU}(p, Fq * g)
	end
end

function encrypt(public_key::Public_Key{NTRU}, arr)
	p, pub = public_key.params, public_key.key
	segment_size = p.N
	arr = partition(arr, segment_size)
	arr = Vector.(arr)
	return map((x) -> p.p  * pub * ringify(T(p.d, p.d, p.N), p.q, p.N) + ringify(x, p.q, p.N), arr)
end

function decrypt(private_key::Private_Key{NTRU}, cipher)
	p, f, Fp = private_key.params, private_key.f, private_key.Fp
	m = Array{Int}(undef, 0)
	for cip in cipher
		a = map_coefficients((x) -> (k = lift(x); k <= p.q/2 ? k : k-p.q), lift(ringify(f, p.q, p.N) * cip))
		a_lift = change_base_ring(ResidueRing(AbstractAlgebra.Integers{Int}(), p.p), a)
		b = Fp * a_lift
		append!(m, lift.(data(b) |> coefficients |> collect))
	end
	return (m
		|> flatten
		|> collect
	)
end

# Utility functions

function T(d1, d2, N)
	return Int.(shuffle!(vcat(ones(d1), -ones(d2), zeros(N - d1 - d2))))
end

function ringify(coefs, m, N)
	base = AbstractAlgebra.Integers{Int}()
	R, x = PolynomialRing(m == 0 ? base : ResidueRing(base, m), "x")
    S = ResidueRing(R, x^N - 1)
	return S(R(coefs))
end

# Test functions

function test()
	params = rand_NTRU(2, 2^10, 256, 1024, 18773, 187730, 2, 12)
	pri, pub = rand(params)
	data = rand(0:params.p - 1, params.N)
	cip = encrypt(pub, data)
	data_out = decrypt(pri, cip)
	return data_out == data
end

# @assert test()