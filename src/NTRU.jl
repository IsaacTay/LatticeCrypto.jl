using Random
using LinearAlgebra
using Base.Iterators

import Base.rand

using AbstractAlgebra
using Primes
using ProgressMeter

include("LatticeUtils.jl")

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
		elseif q <= (6d + 1)p
			return error("Failed q > (6d + 1)p check")
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
	while true
		f = T(p.d, p.d+1, p.N)
		Fp = Fq = Nothing
		try
			Fq = inv(ringify(f, p.q, p.N))
			Fp = inv(ringify(f, p.p, p.N))
		catch e
			if isa(e, NotInvertibleError)
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

function poly_to_lattice(public_key::Public_Key{NTRU})
	coefs = lift.(public_key.key |> lift |> coefficients)
	n = size(coefs, 1)
	coefs = reverse(coefs)
	cyclic_coefs = zeros(Int, n+1, n)
	cyclic_coefs[:] .= take(cycle(coefs), (n+1)*n)
	cyclic_coefs = cyclic_coefs[1:end-1, end:-1:1]
	return hcat(vcat(Matrix{Int}(I, n, n), zeros(Int, n, n)), vcat(cyclic_coefs, Matrix{Int}(I, n, n) * public_key.params.q))
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

function test_NTRU_LLL() # Test against the sample NTRU given
	p = Params{NTRU}(; N = 7, p = 3, q = 41, d = 2)
	f = [-1, 0, 1, 1, -1, 0, 1]
	pri = Private_Key{NTRU}(p, f, inv(ringify(f, p.p, p.N)))
	pub = Public_Key{NTRU}(p, inv(ringify(f, p.q, p.N)) * ringify([0, -1, -1, 0, 1, 0, 1], p.q, p.N))

	arr = [1, 2, 1]
	cip_arr = encrypt(pub, arr)

	lattice = poly_to_lattice(pub)
	LLL_out = LLL(Float64.(lattice)')	
	LLL_f = round.(Int, LLL_out[1][1:floor(Int, end/2)])
	LLL_pri = Private_Key{NTRU}(p, LLL_f, inv(ringify(LLL_f, p.p, p.N)))
	decrypted_arr = decrypt(LLL_pri, cip_arr)

	M = [1 0 -1 1 0 -1 -1 -1 0  -1 0 1 1 0 ;
	0 1 1 -1 0 1 -1 -1 -1 0 1 0 1 0 ;
	-1 1 0 -1 -1 1 0 -1 0 1 1 0 -1 0 ;
	-1 -1 1 0 -1 1 0 1 0  -1 0 -1 0 1 ;
	-1 1 0 -1 1 0 -1 0 -1 0 -1 0 1 1 ;
	-1 -1 -1 -1 -1 -1 -1 0 0 0 0 0 0 0; 
	0 1 0 1 0 -1 1 -1 -1 0 0 2 0 0 ;
	-8 -1 0 9 0 -1 0 -4 2 6 0 -4 7 -7;
	8 1 0 0 -8 -1 2 0 -5 8 -7 -3 1 6 ;
	0 -9 -2 1 9 -1 0 -6 -3 2 5 0 -5 7 ;
	0 8 0 -9 -1 -8 8 2 7 -11 3 -5 2 2 ;
	1 0 0 9 2 -1 -9 5 -7 6 3 -2 -5 0 ;
	-2 1 9 -1 0 0 -9 2 5 0  -5 7 -6 -3;
	3 2 3 3 -6 2 -6 11 6 8 0 9 5 2]

	show(IOContext(stdout), "text/plain", hcat(LLL_out...)')
	println()

	show(IOContext(stdout), "text/plain", hcat(LLL_out...)' .== M)
	println()
	@show sum(hcat(LLL_out...)' .== M)
	return arr == decrypted_arr
end

function test_rand_NTRU_LLL(params)
	p = params
	pri, pub = rand(p)

	arr = rand(0:2, p.N)
	cip_arr = encrypt(pub, arr)
	lattice = poly_to_lattice(pub)
	LLL_out = LLL(Float64.(lattice)')
	decrypted_arr = zeros(2)
	for i = 1:p.N*2
		try 
			LLL_f = round.(Int, LLL_out[i][1:floor(Int, end/2)])
			# LLL_f = sign.(LLL_f) .* mod.(LLL_f, 2)
			# @show LLL_f
			LLL_pri = Private_Key{NTRU}(p, LLL_f, inv(ringify(LLL_f, p.p, p.N)))
			decrypted_arr = decrypt(LLL_pri, cip_arr)
			if arr == decrypted_arr
				return true
			end
		catch end
	end
	return false
end

function test_multiple(n = 1000)
	success = Vector{Bool}(undef, n)
	p = Progress(n, "Testing: ")
	@threads for i = 1:n
		success[i] = test_rand_NTRU_LLL()
		next!(p)
	end
	finish!(p)
	return sum(success)/n * 100
end

@assert test()
# test_NTRU_LLL()
# test_multiple(100)
# test_rand_NTRU_LLL()