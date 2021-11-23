using LinearAlgebra
using Base.Threads

function hadamard_ratio(m)
	d = size(m, 2)
	return (abs(det(BigInt.(m))) / prod(norm.(view.([m], :, 1:d))))^(1/d)
end

function mew(vi, vj)
    return (vi ⋅ vj)/(norm(vj)^2)
end

# Gram–Schmidt Orthogonal Basis
function gs_ortho(vi, vs...)
    change = [zeros(Float32, size(vi)) for _ in 1:length(vs)]
    @threads for i in 1:length(vs)
        change[i] += mew(vi, vs[i]) * vs[i]
    end
    return vi - sum(change)
    # return vi - sum(@. mew.([vi], vs) .* vs)
end

# Lattice Reduction for 2 vectors
function lattice_reduction(v1, v2)
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
	end
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
            v_star[i] = @views gs_ortho(v[i], v_star[1:i-1]...)
        end
		for j = k-1:-1:1
			v[k] = @views v[k] - round(Int, mew(v[k], v_star[j])) * v[j]
		end
		v_star[k] = @views gs_ortho(v[k], v_star[1:k-1]...)
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

# Test functions

function test_LLL()
	M = [19 2 32 46 3 33;
	15 42 11 0 3 24;
	43 15 0 24 4 16;
	20 44 44 0 18 15;
	0 48 35 16 31 31;
	48 33 32 9 1 29]'

	return LLL(M)
end

# test_LLL()