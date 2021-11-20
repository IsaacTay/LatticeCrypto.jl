using AbstractAlgebra
using Random
using ProgressMeter
using Base.Iterators

struct NTRU
	N::Int
	p::Int
	q::Int
	d::Int
	function NTRU(; N = 67, p = 257, q = 18773, d = 12)
		if gcd(p, q) !== 1
			return error("Failed gcd(p, q) = 1 check")
		elseif gcd(N, q) !== 1
			return error("Failed gcd(N, q) = 1 check")
		# elseif q <= (6d + 1)p
		# 	return error("Failed q > (6d + 1)p check")
		end
		return new(N, p, q, d)
	end
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
	r = ringify(T(p.d, p.d, p.N), p.q, p.N)
	return p.p  * public_key * r + ringify(arr, p.q, p.N)
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

function decrypt(p::NTRU, cipher, pri)
	f, Fp = pri
	m = Array{UInt8}(undef, 0)
	for cip in cipher
		a = map_coefficients((x) -> (k = lift(x); k <= p.q/2 ? k : k-p.q), lift(ringify(f, p.q, p.N) * cip))
		a_lift = change_base_ring(ResidueRing(ZZ, p.p), a)
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

function T(d1, d2, N)
	return Int.(shuffle!(vcat(ones(d1), -ones(d2), zeros(N - d1 - d2))))
end

function ringify(coefs, m, N)
	R, x = PolynomialRing(m == 0 ? ZZ : ResidueRing(ZZ, m), "x")
    S = ResidueRing(R, x^N - 1)
	return S(R(coefs))
end

function test()
	params = NTRU()
	pri, pub = generate_keys(params)
	text = "Corporis ut ea quisquam molestiae impedit porro eos. Eveniet officiis veritatis excepturi ipsa eum qui quod aliquam. Quod voluptatem dolores magnam dolores sequi ipsa. Dolor voluptate autem odio culpa qui ea. Non voluptatem ducimus temporibus rerum nulla id."
	cip = encrypt(params, text, pub)
	decrypt(params, cip, pri)
end

test()