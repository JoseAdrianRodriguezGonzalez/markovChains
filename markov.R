#install.packages("igraph")
install.packages("igraph", verbose = TRUE)

crear_grafo <- function(habitacion, aristas, graficar = TRUE) {
  g <- graph(edges = aristas, directed = TRUE)
  if (graficar) {
    plot(g, vertex.size = 30, vertex.color = "lightblue",
         edge.arrow.size = 0.5, vertex.label.cex = 1.2,
         main = "Mapa de la vivienda")
  }
  return(g)
}

habitaciones <- c("Recámara", "Sala", "Cocina", "Baño")
aristas <- c("Sala", "Cocina",
             "Sala", "Baño",
             "Sala", "Sala",
             "Sala", "Recámara",
             "Cocina", "Sala",
             "Cocina", "Recámara",
             "Cocina", "Cocina",
             "Cocina", "Baño",
             "Baño", "Sala",
             "Baño", "Recámara",
             "Baño", "Cocina",
             "Baño", "Baño",
             "Recámara", "Sala",
             "Recámara", "Cocina",
             "Recámara", "Baño",
             "Recámara", "Recámara")
crear_grafo(habitaciones, aristas)
matriz_transicion <- function(estados, pasos) {
  secuencia <- sample(1:estados, pasos, replace = TRUE)
  frecuencias <- matrix(0, nrow = estados, ncol = estados)
  for (i in 1:(length(secuencia) - 1)) {
    actual <- secuencia[i]
    siguiente <- secuencia[i + 1]
    frecuencias[actual, siguiente] <- frecuencias[actual, siguiente] + 1
  }
  m <- frecuencias / rowSums(frecuencias)
  return(m)
}

P <- matriz_transicion(length(habitaciones), 288)

trayectoria <- function(pasos, estado_inicial, matriz) {
  transicion <- numeric(pasos)
  transicion[1] <- estado_inicial
  for (i in 2:pasos) {
    transicion[i] <- sample(1:nrow(matriz), size = 1, prob = matriz[transicion[i - 1], ])
  }
  return(transicion)
}

simulacion_ndias <- function(dias, P, pasos, hab, plotit = TRUE) {
  ndias <- matrix(0, nrow = dias, ncol = pasos)
  ndias[1, ] <- trayectoria(pasos, 1, P)
  for (i in 2:dias) {
    ndias[i, ] <- trayectoria(pasos, ndias[i - 1, pasos], P)
  }
  probabilidades <- apply(ndias, 2, function(col) {
    prop.table(table(factor(col, levels = 1:length(hab))))
  })
  if (plotit) {
    graficar(probabilidades = probabilidades, ndias = ndias, hab = hab)
  }
  return(probabilidades)
}

graficar <- function(barl = TRUE, sequencePLot = TRUE, probabilidades, ndias, hab = hab) {
  if (sequencePLot) {
    matplot(t(probabilidades), type = "l", col = c("red", "blue", "green", "purple"),
            lty = 1, lwd = 2, xlab = "Tiempo (en pasos de 5 minutos)",
            ylab = "Probabilidad",
            main = "Probabilidad de estar en cada habitación a lo largo del día")
    legend("topright", legend = hab, col = c("red", "blue", "green", "purple"), lty = 1, lwd = 2)
  }
  if (barl) {
    hist(ndias[, nrow(probabilidades)], breaks = 0.5 + 0:4,
         xaxt = "n", col = "skyblue",
         main = "Distribución del estado final del día",
         xlab = "Habitación")
    axis(1, at = 1:4, labels = c("Sala", "Cocina", "Baño", "Recámara"))
  }
}

probabilidades <- simulacion_ndias(100, P, 288, habitaciones)
identificar_recurrentes_aprox <- function(P, max_iter = 100, nombres_estados = NULL) {
  estados <- nrow(P)
  recurrentes <- rep(FALSE, estados)
  acc <- diag(estados)
  for (i in 1:max_iter) {
    acc <- acc %*% P
    recurrentes <- recurrentes | (diag(acc) > 0)
  }
  if (!is.null(nombres_estados)) {
    return(nombres_estados[which(recurrentes)])
  } else {
    return(which(recurrentes))
  }
}

recur <- identificar_recurrentes_aprox(P, 100, habitaciones)
crear_estados <- function(actividades_por_habitacion) {
  estados <- unlist(lapply(names(actividades_por_habitacion), function(hab) {
    paste(actividades_por_habitacion[[hab]], "en", hab)
  }))
  return(estados)
}

crear_matriz_emision <- function(estados_actividades, habitaciones) {
  n_estados <- length(estados_actividades)
  n_obs <- length(habitaciones)
  B <- matrix(0, nrow = n_estados, ncol = n_obs)
  for (i in 1:n_estados) {
    actividad_hab <- strsplit(estados_actividades[i], " en ")[[1]][2]
    B[i, which(habitaciones == actividad_hab)] <- 1
  }
  return(B)
}

crear_pi_inicial <- function(n_estados) {
  rep(1 / n_estados, n_estados)
}

simular_HMM <- function(pasos, A, B, pi) {
  n_estados <- nrow(A)
  n_obs <- ncol(B)
  estados_ocultos <- numeric(pasos)
  observaciones <- numeric(pasos)
  estados_ocultos[1] <- sample(1:n_estados, size = 1, prob = pi)
  observaciones[1] <- sample(1:n_obs, size = 1, prob = B[estados_ocultos[1], ])
  for (t in 2:pasos) {
    estados_ocultos[t] <- sample(1:n_estados, size = 1, prob = A[estados_ocultos[t - 1], ])
    observaciones[t] <- sample(1:n_obs, size = 1, prob = B[estados_ocultos[t], ])
  }
  return(list(estados_ocultos = estados_ocultos, observaciones = observaciones))
}

viterbi <- function(obs, A, B, pi) {
  n_obs <- length(obs)
  n_states <- nrow(A)
  T1 <- matrix(0, nrow = n_states, ncol = n_obs)
  T2 <- matrix(0, nrow = n_states, ncol = n_obs)
  for (s in 1:n_states) {
    T1[s, 1] <- pi[s] * B[s, obs[1]]
  }
  for (t in 2:n_obs) {
    for (s in 1:n_states) {
      prob_vec <- T1[, t - 1] * A[, s] * B[s, obs[t]]
      T1[s, t] <- max(prob_vec)
      T2[s, t] <- which.max(prob_vec)
    }
  }
  Z <- numeric(n_obs)
  Z[n_obs] <- which.max(T1[, n_obs])
  for (t in (n_obs - 1):1) {
    Z[t] <- T2[Z[t + 1], t + 1]
  }
  return(Z)
}

# Definiciones para simulación
actividades_por_habitacion <- list(
  "Recámara" = c("Dormir", "Vestirse", "Leer"),
  "Baño" = c("Asearse", "Lavarse los dientes", "Hacer necesidades"),
  "Cocina" = c("Cocinar", "Comer", "Cortar alimentos"),
  "Sala" = c("Ver televisión", "Sentarse sofá", "Leer el periódico")
)

estados <- crear_estados(actividades_por_habitacion)
A <- matriz_transicion(length(estados), 288)
B <- crear_matriz_emision(estados, habitaciones)
pi <- crear_pi_inicial(length(estados))

resultado_HMM <- simular_HMM(pasos = 288, A = A, B = B, pi = pi)
obs_seq <- resultado_HMM$observaciones
actividades_ocultas <- estados[resultado_HMM$estados_ocultos]
habitaciones_observadas <- habitaciones[resultado_HMM$observaciones]

estados_viterbi <- viterbi(obs_seq, A, B, pi)
actividades_estimadas <- estados[estados_viterbi]
montecarlo <- function(simulaciones, T = 24, estados, habitaciones) {
  resultados <- list()
  tiempos_habitaciones <- matrix(0, nrow = simulaciones, ncol = length(habitaciones))
  colnames(tiempos_habitaciones) <- habitaciones
  visitas_hora <- matrix(0, nrow = simulaciones, ncol = T)
  colnames(visitas_hora) <- paste0("Hora_", 1:T)
  estados_hora <- matrix(0, nrow = simulaciones, ncol = T)
  colnames(estados_hora) <- paste0("Hora_", 1:T)
  actividades <- matrix(0, nrow = simulaciones, ncol = length(estados))
  colnames(actividades) <- estados
  
  A <- matriz_transicion(length(estados), 288)
  B <- crear_matriz_emision(estados, habitaciones)
  pi <- crear_pi_inicial(length(estados))
  
  for (i in 1:simulaciones) {
    sim <- simular_HMM(T, A, B, pi)
    obs <- habitaciones[sim$observaciones]
    est <- estados[sim$estados_ocultos]
    tiempos_habitaciones[i, ] <- as.numeric(table(factor(obs, levels = habitaciones)))
    visitas_hora[i, ] <- sim$observaciones
    estados_hora[i, ] <- sim$estados_ocultos
    actividades[i, ] <- as.numeric(table(factor(est, levels = estados)))
  }
  
  resultados$tiempos_por_habitacion <- tiempos_habitaciones
  resultados$visitas_por_hora <- visitas_hora
  resultados$estados_por_hora <- estados_hora
  resultados$actividades_totales <- actividades
  return(resultados)
}
