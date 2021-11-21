using Random
using ProgressMeter
using Base.Iterators

using AbstractAlgebra
using Primes

struct NTRU
	N::Int
	p::Int
	q::Int
	d::Int
	function NTRU(; N = 67, p = 257, q = 18773, d = 12)
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
		return new(N, p, q, d)
	end
end

function rand_NTRU(N_min, N_max, p_min, p_max, q_min, q_max, d_min, d_max)
	N = rand(primes(N_min, N_max))
	p = rand(primes(p_min, p_max))
	q = rand(primes(q_min, q_max))
	d = rand(d_min:d_max)
	return NTRU(; N, p, q, d)
end

function generate_keys(p::NTRU)
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
		return ((f, Fp), Fq * g)
	end
end

function encrypt(p::NTRU, arr, public_key)
	segment_size = p.N
	arr = partition(arr, segment_size)
	arr = Vector.(arr)
	r = ringify(T(p.d, p.d, p.N), p.q, p.N)
	return map((x) -> p.p  * public_key * ringify(T(p.d, p.d, p.N), p.q, p.N) + ringify(x, p.q, p.N), arr)
end

function encrypt(p::NTRU, text::String, public_key)
	segment_size = p.N
	text = Int.(codeunits(text))
	#text = vcat(text, [0x00 for _ in 1:segment_size-(length(text)%segment_size)])
	text = partition(text, segment_size) |> collect
	text = Vector.(text)
	r = ringify(T(p.d, p.d, p.N), p.q, p.N)
	b = [p.p  * public_key * r] .+ ringify.(text, p.q, p.N)
end

function decrypt_string(p::NTRU, cipher, pri)
	f, Fp = pri
	m = Array{UInt8}(undef, 0)
	for cip in cipher
		a = map_coefficients((x) -> (k = lift(x); k <= p.q/2 ? k : k-p.q), lift(ringify(f, p.q, p.N) * cip))
		a_lift = change_base_ring(ResidueRing(AbstractAlgebra.Integers{Int}(), p.p), a)
		b = Fp * a_lift
		append!(m, UInt8.(lift.(data(b) |> coefficients |> collect)))
	end
	return (m
		|> flatten
		|> (x) -> Iterators.filter((y) -> y !== 0x00, x)
		|> collect
		|> String
	)
end

function decrypt(p::NTRU, cipher, pri)
	f, Fp = pri
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

function T(d1, d2, N)
	return Int.(shuffle!(vcat(ones(d1), -ones(d2), zeros(N - d1 - d2))))
end

function ringify(coefs, m, N)
	base = AbstractAlgebra.Integers{Int}()
	R, x = PolynomialRing(m == 0 ? base : ResidueRing(base, m), "x")
    S = ResidueRing(R, x^N - 1)
	return S(R(coefs))
end

function test()
	params = rand_NTRU(2, 2^10, 256, 1024, 18773, 187730, 2, 12)
	pri, pub = generate_keys(params)
	data = rand(0:params.p - 1, params.N)
	cip = encrypt(params, data, pub)
	data_out = decrypt(params, cip, pri)
	return data_out == data
end

test()