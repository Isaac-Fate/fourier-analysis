using Plots
using LaTeXStrings

begin
    println("Basic Properties of Fourier Series")
    figures_dir = joinpath(@__DIR__, "../src/assets/figures")
    default(dpi=150)
end

#=
Trigonometric polynomials
=#
begin
    epsilon = 0.1
    function t(theta::Real; k::Integer)
        return (epsilon + cos(theta))^k
    end

    plot(
        xticks=(-π:π/2:π, [L"-\pi", L"-\frac{\pi}{2}", "0", L"\frac{\pi}{2}", L"\pi"]),
    )
    thetas = range(-π, π; length=1000)
    for k in [1, 2, 5, 10]
        t_partial = theta -> t(theta; k=k)
        plot!(thetas, t_partial.(thetas), label=latexstring("k=$(k)"))
    end

    # Line y = 0
    plot!([-π, π], [0, 0]; color=:black, linestyle=:dash, label=L"y=0")

    display(current())

    savefig(joinpath(figures_dir, "sequence-of-trigonometric-polynomials.png"))
end

#=
Fejer kernals
=#
begin
    function fejer(x::Real; n::Integer)
        return 1 / n * (sin(n * x / 2) / sin(x / 2))^2
    end

    plot(
        xticks=(-π:π/2:π, [L"-\pi", L"-\frac{\pi}{2}", "0", L"\frac{\pi}{2}", L"\pi"]),
    )
    xs = range(-π, π; length=1000)
    for n in 2:2:10
        fejer_partial = x -> fejer(x; n=n)
        plot!(xs, fejer_partial.(xs), label=latexstring("N=$(n)"))
    end

    display(current())

    savefig(joinpath(figures_dir, "fejer-kernels.png"))
end

#=
Dirichlet kernals
=#
begin
    function dirichlet(x::Real; n::Integer)
        return sin((n + 1 / 2) * x) / sin(x / 2)
    end

    plot(
        xticks=(-π:π/2:π, [L"-\pi", L"-\frac{\pi}{2}", "0", L"\frac{\pi}{2}", L"\pi"]),
    )
    xs = range(-π, π; length=1000)
    for n in 2:2:10
        dirichlet_partial = x -> dirichlet(x; n=n)
        plot!(xs, dirichlet_partial.(xs), label=latexstring("N=$(n)"))
    end

    display(current())

    savefig(joinpath(figures_dir, "dirichlet-kernels.png"))
end


begin
    r = 0.1
    N = 100
    L = 1000
    cs = randn(ComplexF64, L)

    # Create partial sums
    ss = zeros(ComplexF64, L)
    ss[1] = cs[1]
    for n in 2:L
        ss[n] = cs[n] + ss[n-1]
    end

    # Cesàro sums
    sigmas = zeros(ComplexF64, L)
    for n in 1:L
        sigmas[n] = sum(ss[1:n]) / n
    end

    # Exponents of r
    r_pows = r .^ (1:L)

    lhs = sum(cs[1:N] .* r_pows[1:N])
    rhs1 = (1 - r) * sum(ss[1:N] .* r_pows[1:N]) + ss[N] * r_pows[N+1]
    rhs2 = (1 - r)^2 * sum((1:N) .* sigmas[1:N] .* r_pows[1:N]) + (1 - r) * N * sigmas[N] * r_pows[N+1] + ss[N] * r_pows[N+1]

    @assert isapprox(lhs, rhs1)
    @assert isapprox(lhs, rhs2)
end

#=
Poisson kernals
=#
begin
    function poisson(theta::Real; r::Real)
        return (1 - r^2) / (1 - 2r * cos(theta) + r^2)
    end

    plot(
        xticks=(-π:π/2:π, [L"-\pi", L"-\frac{\pi}{2}", "0", L"\frac{\pi}{2}", L"\pi"]),
    )
    xs = range(-π, π; length=1000)
    for r in 0.1:0.2:0.9
        poisson_partial = x -> poisson(x; r=r)
        plot!(xs, poisson_partial.(xs), label=latexstring("r=$(r)"))
    end

    xlabel!(L"\theta")

    display(current())

    savefig(joinpath(figures_dir, "poisson-kernels.png"))
end