using Base.Iterators
using Base.Threads
using LinearAlgebra

import Base.rand

using ProgressMeter

include("LatticeUtils.jl")

abstract type GGH end

struct Params{GGH}
	n::Int # Key Size
	delta::Int # Perturbation Size
	function Params{GGH}(; n = 10, delta = 10)
		if n <= 0
			return error("Size of key has to be greater than 1")
		end
		return new{GGH}(n, delta)
	end
end

struct Private_Key{GGH}
	params::Params{GGH}
	key::Matrix{<:Integer}
	unimod::Matrix{<:Integer}
end

struct Public_Key{GGH}
	params::Params{GGH}
	key::Matrix{<:Integer}
end

function rand(params::Params{GGH}; d = 100)
	n = params.n
	sqrt_n = sqrt(n)
	k = 10
	private_key = Matrix{Int}(undef, n, n)
    p = ProgressUnknown("Private Keys Tried:");
	r = vcat(1:d, -1:-1:-d)
    while true
		temp = [rand(r, n) for _ in 1:n]
		temp_star = [Vector{Float32}(undef, n) for _ in 1:n]
		temp_star[1] = temp[1]
		for i = 2:n
			temp_star[i] = @views gs_ortho(temp[i], temp_star[1:i-1]...)
		end
		for i in 1:n
			temp[i] = round.(Int, (sqrt_n*10^k / norm(temp_star[i])) .* temp_star[i])
		end
		private_key = hcat(temp...)
		ratio = hadamard_ratio(private_key)
		0.9 < ratio < 1 && break
		next!(p; showvalues = [(:ratio, ratio)])
		# hadamard_ratio(private_key) < 0.9 || hadamard_ratio(private_key) > 1 || break
	end
	
	p = ProgressUnknown("Unimodular Matrices Tried:");
	unimod = public_key = Matrix{Int}(undef, n, n)
	while true
		unimod = rand_unimod(n)
		public_key = unimod * private_key
		ratio = hadamard_ratio(public_key)
		0.001 < ratio < 0.1 && break
		# hadamard_ratio(public_key) > 0.1 || hadamard_ratio(public_key) < 0.000001 || break
		next!(p; showvalues = [(:ratio, ratio)])
	end
	return Private_Key{GGH}(params, private_key, unimod), Public_Key{GGH}(params, public_key)
end


function encrypt(public_key::Public_Key{GGH}, arr)
	pub = public_key.key
	delta = public_key.params.delta
	segment_size = size(pub, 2)
	arr = vcat(arr, [0x00 for _ in 1:segment_size-(length(arr)%segment_size)])
	arr = partition(arr, segment_size) |> collect
	out = Vector{Matrix{Integer}}(undef, size(arr, 1))
	r = rand(-delta: delta, segment_size, size(arr, 1))
	@simd for i in 1:size(arr, 1)
		out[i] = arr[i]' * pub + r[:, i]'
	end
	return out
end

function decrypt(private_key::Private_Key{GGH}, cipher_arr)
	pri, uni = private_key.key, private_key.unimod
	decrypted_arr = Vector{Matrix{Integer}}(undef, size(cipher_arr, 1))
	@simd for i in 1:size(cipher_arr, 1)
		decrypted_arr[i] = round.(Integer, (round.(cipher_arr[i] / pri) / uni))
	end
	return (hcat(decrypted_arr...)
		|> flatten
		|> (x) -> Iterators.filter((y) -> y !== zero(Integer), x)
		|> collect
	)
end

function rand_unimod(n; d=10)
	@assert n > 0
	r = rand(-d:d, n, n)
	@views r = r .- ((r .+ rand([-1 1], n, n)) .* Matrix(I, n, n))
	return @views triu(r) * tril(r) * triu(r[end:-1:1, :]) * tril(r[end:-1:1, :])
end

# Test functions

function test_ggh(; n = 3)
	text = "Corporis ut ea quisquam molestiae impedit porro eos. Eveniet officiis veritatis excepturi ipsa eum qui quod aliquam. Quod voluptatem dolores magnam dolores sequi ipsa. Dolor voluptate autem odio culpa qui ea. Non voluptatem ducimus temporibus rerum nulla id."
	# text = text^10000
	arr = codeunits(text)
	pri, pub = rand(Params{GGH}(; n))
	cipher_arr = encrypt(pub, arr)
	decrypt_arr = decrypt(pri, cipher_arr)
	# @show String(UInt8.(decrypt_arr))
	return decrypt_arr == arr
end

function test_consistency(; n = 3, d = 10000)
	success = Vector{Bool}(undef, d)
	p = Progress(d)
	for i in 1:d
		success[i] = test_ggh(; n)
		next!(p)
	end
	return sum(success) / d
end

# @assert test_ggh()
# @show test_consistency()