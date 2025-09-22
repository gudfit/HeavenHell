
import pandas as pd
import matplotlib.pyplot as plt
import matplotlib.style as style

def plot_results():
    """
    Loads the simulation data and generates a clean, publication-style plot.
    """
    try:
        data = pd.read_csv('results.csv')
    except FileNotFoundError:
        print("Error: results.csv not found. Please run the simulation first.")
        return

    # Get the max_rest value, which is the theoretical phase transition point
    if 'max_rest' not in data.columns or data.empty:
        print("Error: 'max_rest' column not in results.csv or file is empty.")
        return
    max_rest = data['max_rest'][0]

    # Use a style that is clean and suitable for academic papers
    style.use('seaborn-v0_8-whitegrid')

    # Create the plot with a specific size
    fig, ax = plt.subplots(figsize=(10, 6))

    # Plot the two data series with calm, distinct colors and styles
    ax.plot(data['W'], data['percent_glory_sync'], 
            label='Synchronous Update (% Glory)', 
            color='#4c72b0', # A calm blue
            linewidth=2)
            
    ax.plot(data['W'], data['success_prob_async'], 
            label='Asynchronous Update (Success Rate)', 
            color='#55a868', # A calm green
            linestyle='--',
            linewidth=2)

    # Add a vertical dashed line to mark the theoretical phase transition
    ax.axvline(x=max_rest, 
               color='#c44e52', # A calm red
               linestyle=':', 
               linewidth=2.5, 
               label=f'Phase Transition (max_rest = {max_rest})')

    # Set titles and labels with appropriate font sizes for clarity
    ax.set_title('System Convergence to "Glory" vs. Hub Weight (W)', fontsize=15, pad=20)
    ax.set_xlabel('Hub Broadcast Weight (W)', fontsize=12)
    ax.set_ylabel('Success Rate / % of Nodes in "Glory"', fontsize=12)

    # Add a legend
    ax.legend(fontsize=10, frameon=True)

    # Set axis limits to keep the plot tidy
    ax.set_ylim(-0.05, 1.05)
    ax.set_xlim(0, data['W'].max())

    # Save the figure with high resolution for clarity
    plt.savefig('heaven_hell_plot.png', dpi=300, bbox_inches='tight')
    print("Plot saved as heaven_hell_plot.png")

if __name__ == "__main__":
    plot_results()
