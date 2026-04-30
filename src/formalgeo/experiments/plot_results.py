import matplotlib.pyplot as plt
import pandas as pd
import numpy as np
import os

def plot_ablation_study(results_dict, output_path='results/correct_proofs_ablation.png'):
    """
    Plots the ablation study results as seen in the provided image.
    
    Args:
        results_dict (dict): Dictionary where keys are model/variant names and values are 
                           lists of success rates (%) for levels 1-5.
        output_path (str): Path to save the resulting plot.
    """
    # Define styles for each series based on the target image
    # Blue shades for Analogy-based, Red shades for Base model
    styles = {
        'Analogy-based - 1 run, no retries': {'color': '#1f77b4', 'marker': 'o', 'linestyle': '-'},
        'Analogy-based - 1 run, 5 retries (w\\ verifier)': {'color': '#1f77b4', 'marker': 's', 'linestyle': '--'},
        'Analogy-based - 3 runs, 5 retries (w\\ verifier)': {'color': '#1f77b4', 'marker': '^', 'linestyle': ':'},
        'Base model - 1 run, no retries': {'color': '#d62728', 'marker': 'o', 'linestyle': '-', 'markerfacecolor': 'white'},
        'Base model - 1 run, 5 retries (w\\ verifier)': {'color': '#d62728', 'marker': 's', 'linestyle': '--', 'markerfacecolor': 'white'},
        'Base model - 3 runs, 5 retries (w\\ verifier)': {'color': '#d62728', 'marker': '^', 'linestyle': ':', 'markerfacecolor': 'white'},
    }

    # Prepare the figure
    plt.figure(figsize=(12, 10), dpi=300)
    
    levels = np.arange(1, 6)
    
    for label, values in results_dict.items():
        style = styles.get(label, {'color': None, 'marker': 'o', 'linestyle': '-'})
        plt.plot(levels, values, label=label, **style, markersize=10, linewidth=2)

    # Customize the plot
    plt.title('% correct proofs per level of difficulty', fontsize=28, fontweight='bold', pad=25)
    plt.xlabel('Level', fontsize=26, fontweight='bold')
    plt.ylabel('Correct Proofs (%)', fontsize=26, fontweight='bold')
    
    plt.xticks(levels, fontsize=24, fontweight='bold')
    plt.yticks(np.arange(0, 110, 10), fontsize=24, fontweight='bold')
    
    plt.ylim(-5, 105)
    plt.xlim(0.8, 5.2)
    
    # Legend configuration
    plt.legend(loc='upper center', bbox_to_anchor=(0.5, -0.12),
               shadow=False, ncol=1, frameon=True, edgecolor='black',
               prop={'weight': 'bold', 'size': 22})
    
    plt.grid(True, axis='y', linestyle='-', alpha=0.3, color='gray')
    
    # Ensure tight layout to save the legend
    plt.tight_layout()
    
    # Save the plot
    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    plt.savefig(output_path, bbox_inches='tight')
    print(f"Plot saved to {output_path}")
    plt.close()



if __name__ == "__main__":
    sample_data_claude_sonnet_4_6 = {
        'Analogy-based - 1 run, no retries': [100, 90, 60, 30, 20],
        'Analogy-based - 1 run, 5 retries (w\\ verifier)': [100, 100, 70, 60, 60],
        'Analogy-based - 3 runs, 5 retries (w\\ verifier)': [100, 100, 80, 70, 80],
        'Base model - 1 run, no retries': [60, 30, 20, 20, 10],
        'Base model - 1 run, 5 retries (w\\ verifier)': [80, 70, 30, 70, 40],
        'Base model - 3 runs, 5 retries (w\\ verifier)': [90, 90, 60, 80, 70],
    }

    sample_data_gemini_flash_2_5 = {
        'Analogy-based - 1 run, no retries': [90, 80, 30, 20, 20],
        'Analogy-based - 1 run, 5 retries (w\\ verifier)': [100, 100, 70, 50, 50],
        'Analogy-based - 3 runs, 5 retries (w\\ verifier)': [100, 100, 80, 100, 50],
        'Base model - 1 run, no retries': [40, 20, 20, 20, 10],
        'Base model - 1 run, 5 retries (w\\ verifier)': [80, 80, 30, 50, 50],
        'Base model - 3 runs, 5 retries (w\\ verifier)': [100, 80, 60, 70, 50],
    }

    sample_data_gpt_o1 = {
        'Analogy-based - 1 run, no retries': [90, 80, 30, 20, 20],
        'Analogy-based - 1 run, 5 retries (w\\ verifier)': [100, 100, 60, 50, 30],
        'Analogy-based - 3 runs, 5 retries (w\\ verifier)': [100, 100, 70, 80, 50],
        'Base model - 1 run, no retries': [40, 10, 0, 0, 0],
        'Base model - 1 run, 5 retries (w\\ verifier)': [70, 50, 30, 20, 10],
        'Base model - 3 runs, 5 retries (w\\ verifier)': [80, 100, 30, 40, 10],
    }

    sample_data_gpt_5 = {
        'Analogy-based - 1 run, no retries': [90, 80, 50, 60, 40],
        'Analogy-based - 1 run, 5 retries (w\\ verifier)': [100, 100, 100, 90, 90],
        'Analogy-based - 3 runs, 5 retries (w\\ verifier)': [100, 100, 100, 90, 90],
        'Base model - 1 run, no retries': [90, 40, 20, 50, 20],
        'Base model - 1 run, 5 retries (w\\ verifier)': [100, 80, 80, 90, 50],
        'Base model - 3 runs, 5 retries (w\\ verifier)': [100, 80, 90, 90, 80],
    }
    

    plot_ablation_study(sample_data_claude_sonnet_4_6, 'results/correct_proofs_ablation_claude.png')
    plot_ablation_study(sample_data_gemini_flash_2_5, 'results/correct_proofs_ablation_gemini.png')
    plot_ablation_study(sample_data_gpt_5, 'results/correct_proofs_ablation_gpt5.png')
    plot_ablation_study(sample_data_gpt_o1, 'results/correct_proofs_ablation_gpt_o1.png')


