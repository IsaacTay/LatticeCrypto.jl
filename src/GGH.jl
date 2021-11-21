using LinearAlgebra
using Base64
using Base.Iterators
using Base.Threads

using ProgressMeter
using ProgressMeter: @showprogress

function encrypt(text::String, public_key, delta = 1)
	segment_size = size(public_key, 2)
	text = codeunits(text)
	text = vcat(text, [0x00 for _ in 1:segment_size-(length(text)%segment_size)])
	text = partition(text, segment_size) |> collect
	out = Vector{Matrix{Int64}}(undef, size(text, 1))
	r = rand(-delta: delta, segment_size, size(text, 1))
	@simd for i in 1:size(text, 1)
		out[i] = transpose(text[i]) * public_key + r[:, i]'
	end
	# @time (transpose.(text) .* [public_key]) .+ [rand(-delta:delta, 1, segment_size) for _ in 1:size(text, 1)]
	return out
end


function encrypt(arr, public_key, delta = 1)
	segment_size = size(public_key, 2)
	arr = vcat(arr, [0x00 for _ in 1:segment_size-(length(arr)%segment_size)])
	arr = partition(arr, segment_size) |> collect
	out = Vector{Matrix{Int64}}(undef, size(arr, 1))
	r = rand(-delta: delta, segment_size, size(arr, 1))
	@simd for i in 1:size(arr, 1)
		out[i] = transpose(arr[i]) * public_key + r[:, i]'
	end
	# @time (transpose.(arr) .* [public_key]) .+ [rand(-delta:delta, 1, segment_size) for _ in 1:size(arr, 1)]
	return out
end

function decrypt(cipher_arr, private_key, unimod)
	# @time decrypted_arr = @. ((x) -> round(UInt8, x))(((x) -> round(x))(cipher_arr / [private_key]) / [BigInt(unimod)])
	decrypted_arr = Vector{Matrix{UInt8}}(undef, size(cipher_arr, 1))
	@simd for i in 1:size(cipher_arr, 1)
		decrypted_arr[i] = round.(UInt8, (round.(cipher_arr[i] / private_key) / unimod))
	end
	return (hcat(decrypted_arr...)
		|> flatten
		|> (x) -> Iterators.filter((y) -> y !== 0x00, x)
		|> collect
		|> String
	)
end

function generate_keys(n, d=100)
	@assert n > 0
	#private_key = Matrix{Int}(undef, n, n)
    best_key = [rand(vcat(1:d, -1:-1:-d), n) for _ in 1:n]
	best_ratio = hadamard_ratio(hcat(best_key...))
	p = ProgressUnknown("Private Keys Tried:");
	r = vcat(1:d, -1:-1:-d)
    while true
		temp = [rand(r, n) for _ in 1:n]
		gs_temp = Vector{Vector{Int}}(undef, n)
		gs_best = Vector{Vector{Int}}(undef, n)
		gs_temp[1] = @views deepcopy(temp[1])
		gs_best[1] = @views deepcopy(best_key[1])
        for i in 2:n
            gs_temp[i] = @views gs(temp[i], gs_temp[1:i-1]...)
			gs_best[i] = @views gs(best_key[i], gs_best[1:i-1]...)
        end
		ratios = [(temp, hadamard_ratio(hcat(temp...))), (gs_temp, hadamard_ratio(hcat(gs_temp...))), (gs_best, hadamard_ratio(hcat(gs_best...))), (best_key, best_ratio)]
		best_index = (i[2] for i in ratios) |> collect |> argmax 
		best_key, best_ratio = ratios[best_index]
		0.9 < best_ratio <= 1 && break
		next!(p; showvalues = [(:ratio, best_ratio)])
		# hadamard_ratio(private_key) < 0.9 || hadamard_ratio(private_key) > 1 || break
	end
	private_key = hcat(best_key...)
	
	unimod = public_key = Matrix{Int}(undef, n, n)
	while true
		unimod = rand_unimod(n)
		public_key = unimod * private_key
		0.00001 <= hadamard_ratio(public_key) < 0.1 && break
		# hadamard_ratio(public_key) > 0.1 || hadamard_ratio(public_key) < 0.000001 || break
	end
	return private_key, public_key, unimod
end

function hadamard_ratio(m)
	m = @views m
	d = size(m, 2)
	return (abs(det(BigInt.(m))) / prod(norm.(view.([m], :, 1:d))))^(1/d)
end

function rand_unimod(n, d=10, trials=300)
	@assert n > 0
	#r = [zeros(Int, n, n) for _ in 1:trials]
	#setindex!.(r, rand([-d, d], trials), reduce((x, y) -> cat.(x, y; dims=1), rand(Iterators.filter((x) -> x[1] !== x[2], product(1:n, 1:n)) |> collect, trials); init=([], []))...)
	#r = prod(r .+ [Matrix(I, n, n)])
	#return r
	r = rand(-d:d, n, n)
	@views r = r .- ((r .+ rand([-1 1], n, n)) .* Matrix(I, n, n))
	return @views triu(r) * tril(r) * triu(r[end:-1:1, :]) * tril(r[end:-1:1, :])
end

function test_consistency(n = 3, d = 10000)
	success = zeros(Bool, d)
	p = Progress(d)
	@threads for i in 1:d
		success[i] = test_ggh(n)
		next!(p)
	end
	return sum(success) / d
end

function test_ggh(n = 3)
	text = "Corporis ut ea quisquam molestiae impedit porro eos. Eveniet officiis veritatis excepturi ipsa eum qui quod aliquam. Quod voluptatem dolores magnam dolores sequi ipsa. Dolor voluptate autem odio culpa qui ea. Non voluptatem ducimus temporibus rerum nulla id."
	text = text^10000
	pri, pub, uni = generate_keys(n)
	cipher_arr = encrypt(text, pub)
	decrypt_text = ""
	#decrypt(cipher_arr, pri, uni)
	try
		decrypt_text = decrypt(cipher_arr, pri, uni)
	catch e
		@show pri, pub
		return false
	end
	decrypt_text == text || @show pub, uni
	return decrypt_text == text
end

function LLL(v)
    # v::Vector{Vector{Int64}}
	n = size(v, 2)
    v = getindex.([v], :, 1:n)
	k = 2
	v_star = [Vector{Float32}(undef, size(v, 1)) for _ in 1:n]
    v_star[1] = v[1]
	p = ProgressUnknown("LLL Reduction: "; spinner=true)
	while k <= n
		update!(p; showvalues = [(:k, k)], spinner = "⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏")
		v_star[1] = v[1]
        for i in max(k-1, 2):k
            v_star[i] = @views gs(v[i], v_star[1:i-1]...)
        end
		for j = k-1:-1:1
			v[k] = @views v[k] - round(Int, mew(v[k], v_star[j])) * v[j]
		end
		v_star[k] = @views gs(v[k], v_star[1:k-1]...)
        if @views norm(v_star[k])^2 >= (3/4 - mew(v[k], v_star[k-1])^2) * norm(v_star[k-1])^2
			k = k + 1
		else
			v[k-1], v[k] = v[k], v[k-1]
			k = max(k - 1, 2)
		end
	end
	finish!(p)
	return v
end

function mew(vi, vj)
    return (vi ⋅ vj)/(norm(vj)^2)
end

function gs(vi, vs...)
    change = [zeros(Float32, size(vi)) for _ in 1:length(vs)]
    @threads for i in 1:length(vs)
        change[i] += mew(vi, vs[i]) * vs[i]
    end
    return vi - sum(change)
    # return vi - sum(@. mew.([vi], vs) .* vs)
end

function kgs(v1, v2)
	while true
		if norm(v2) < norm(v1)
			v1, v2 = v2, v1
		end
		m = round.(Int, (v1 ⋅ v2)/norm(v1)^2)
		if m == 0
			return v1, v2
		else
			v2 -= m * v1
		end
        @show v1, v2, m * v1
	end
end

function test_LLL()
	M = [19 2 32 46 3 33;
	15 42 11 0 3 24;
	43 15 0 24 4 16;
	20 44 44 0 18 15;
	0 48 35 16 31 31;
	48 33 32 9 1 29]'

	return LLL(M)
end

test_LLL()