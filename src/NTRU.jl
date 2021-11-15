using AbstractAlgebra
using Random

struct NTRU
	N::Int
	p::Int
	q::Int
	d::Int
	function NTRU(; N = 64, p = 3, q = 41, d = 2)
		if gcd(p, q) !== 1
			return error("Failed gcd(p, q) = 1 check")
		elseif gcd(N, q) !== 1
			return error("Failed gcd(N, q) = 1 check")
		elseif q <= (6d + 1)p
			return error("Failed q > (6d + 1)p check")
		end
		return new(N, p, q, d)
	end
end

function generate_keys(p::NTRU)
	while true
		f = T(p.d, p.d+1, p.N)
		Fp = Fq = Nothing
		try
			Fq = inv(ringify(f, p.q, p.N))
			Fp = inv(ringify(f, p.p, p.N))
		catch
			continue
		end
		g = ringify(T(p.d, p.d, p.N), p.q, p.N);
		return ((f, Fp), Fq * g)
	end
end

function encrypt(p::NTRU, arr, public_key)
	r = ringify(T(p.d, p.d, p.N), p.q, p.N)
	return p.p  * public_key * r + ringify(arr, p.q, p.N)
end


function T(d1, d2, N)
	return Int.(shuffle!(vcat(ones(d1), -ones(d2), zeros(N - d1 - d2))))
end

function ringify(coefs, m, N)
	R, x = PolynomialRing(m == 0 ? ZZ : ResidueRing(ZZ, m), "x")
    S = ResidueRing(R, x^N - 1)
	return S(R(coefs))
end