import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
import random

class IsingModel:
    def __init__(self, size=50, probability_spin_up=0.5):
        # Size of the grid (NxN)
        self.size = size
        # Initial probability of a spin being +1
        self.probability_spin_up = probability_spin_up
        self.grid = None
        # Sum of all spins in the grid (used for magnetization)
        self.sum_of_spins = 0
        # Temperature of the system
        self.temperature = 2.0
        # Whether to use sequential update or shuffled updates
        self.sequential_update = False

    def setup(self):
        """Initialize the spin grid with random values (+1 or -1)"""
        self.grid = np.zeros((self.size, self.size), dtype=int)

        # Generate a random matrix and assign spins based on probability
        rand_matrix = np.random.random((self.size, self.size))
        self.grid[rand_matrix < self.probability_spin_up] = 1
        self.grid[rand_matrix >= self.probability_spin_up] = -1

        # Compute initial total spin
        self.sum_of_spins = np.sum(self.grid)

    def get_neighbors_sum(self, i, j):
        """Calculate the sum of the four nearest neighbors (with periodic boundary conditions)"""
        neighbors_sum = (
            self.grid[(i-1) % self.size, j] +
            self.grid[(i+1) % self.size, j] +
            self.grid[i, (j-1) % self.size] +
            self.grid[i, (j+1) % self.size]
        )
        return neighbors_sum

    def update_patch(self, i, j):
        """Update a single spin using the Metropolis algorithm"""
        current_spin = self.grid[i, j]
        neighbors_sum = self.get_neighbors_sum(i, j)

        # Compute energy difference if the spin is flipped
        Ediff = 2 * current_spin * neighbors_sum

        # Metropolis criterion for spin flip
        if (Ediff <= 0) or (self.temperature > 0 and 
                            random.random() < np.exp(-Ediff / self.temperature)):
            # Flip the spin
            self.grid[i, j] = -current_spin
            # Update the total sum of spins accordingly
            self.sum_of_spins += 2 * self.grid[i, j]

    def go(self):
        """Perform a full simulation step over the entire grid"""
        # Generate list of all grid coordinates
        coordinates = [(i, j) for i in range(self.size) for j in range(self.size)]

        # Shuffle the order unless sequential update is selected
        if not self.sequential_update:
            random.shuffle(coordinates)

        # Update each spin
        for i, j in coordinates:
            self.update_patch(i, j)

    def magnetization(self):
        """Calculate the average magnetization of the system"""
        return self.sum_of_spins / (self.size * self.size)

    def scan_temperature(self, T_start=3.0, T_end=2.0, T_step=0.01, 
                         equilibration_steps=200, measurement_steps=200):
        """Scan over a range of temperatures and collect magnetization data"""
        temperatures = np.arange(T_start, T_end, -T_step)
        magnetizations = []
        fluctuations = []

        print(f"Scanning from T={T_start} to T={T_end} with {len(temperatures)} points...")

        for temp_idx, temp in enumerate(temperatures):
            self.temperature = temp

            # Reset accumulators for this temperature
            n = 0
            summ = 0
            summ2 = 0

            # Simulate the system
            for step in range(equilibration_steps + measurement_steps):
                self.go()

                # Start measuring after equilibration
                if step >= equilibration_steps:
                    n += 1
                    m = self.magnetization()
                    summ += m
                    summ2 += m * m

            # Compute average magnetization and its fluctuations
            avg_magnetization = summ / n
            fluctuation = (n * summ2 - summ * summ) / (n * (n - 1))

            magnetizations.append(avg_magnetization)
            fluctuations.append(fluctuation)

            # Print progress every 10 temperatures
            if temp_idx % 10 == 0:
                print(f"Temperature: {temp:.2f}, Magnetization: {avg_magnetization:.3f}")

        return temperatures, magnetizations, fluctuations

    def visualize_grid(self):
        """Display the current state of the grid"""
        plt.figure(figsize=(8, 8))
        # Color map: blue for +1, red for -1
        display_grid = np.where(self.grid == 1, 1, 0)
        plt.imshow(display_grid, cmap='RdBu', vmin=0, vmax=1)
        plt.title(f'Ising Model Grid (T={self.temperature:.2f})')
        plt.colorbar(label='Spin')
        plt.show()

def main():
    # Create and initialize the Ising model
    model = IsingModel(size=50, probability_spin_up=0.5)
    model.setup()

    print("Starting temperature scan...")

    # Run the temperature scan
    temperatures, magnetizations, fluctuations = model.scan_temperature(
        T_start=3.0, T_end=2.0, T_step=0.001,
        equilibration_steps=200, measurement_steps=200
    )

    # Create plots for magnetization and fluctuations
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(15, 6))

    # Plot magnetization vs temperature
    ax1.plot(temperatures, np.abs(magnetizations), 'b-', linewidth=2)
    ax1.set_xlabel('Temperature')
    ax1.set_ylabel('|Magnetization|')
    ax1.set_title('Magnetization vs Temperature')
    ax1.grid(True, alpha=0.3)
    ax1.set_xlim(2.0, 3.0)

    # Plot fluctuations vs temperature
    ax2.plot(temperatures, fluctuations, 'r-', linewidth=2)
    ax2.set_xlabel('Temperature')
    ax2.set_ylabel('Fluctuations')
    ax2.set_title('Fluctuations vs Temperature')
    ax2.grid(True, alpha=0.3)
    ax2.set_xlim(2.0, 3.0)

    plt.tight_layout()
    plt.show()

    # Display the final grid state
    model.visualize_grid()

    print("Temperature scan complete!")
    print(f"Theoretical critical temperature for 2D Ising model: ~2.269")

if __name__ == "__main__":
    main()
