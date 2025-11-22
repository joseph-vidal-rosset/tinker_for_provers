// G4-cim Web Interface Client (CGI version)
// Appelle directement le script CGI - pas de serveur permanent

const API_URL = '/G4-cim/g4cim.cgi';  // Script CGI appelé par Apache

// Initialize event listeners
document.addEventListener('DOMContentLoaded', () => {
    const proveBtn = document.getElementById('prove-btn');
    const clearBtn = document.getElementById('clear-btn');
    const formulaInput = document.getElementById('formula');
    const exampleBtns = document.querySelectorAll('.example-btn');

    proveBtn.addEventListener('click', handleProve);
    clearBtn.addEventListener('click', handleClear);
    formulaInput.addEventListener('keypress', (e) => {
        if (e.key === 'Enter') handleProve();
    });

    exampleBtns.forEach(btn => {
        btn.addEventListener('click', () => {
            formulaInput.value = btn.dataset.formula;
            const mode = btn.dataset.mode;
            document.querySelector(`input[name="mode"][value="${mode}"]`).checked = true;
        });
    });
});

async function handleProve() {
    const formula = document.getElementById('formula').value.trim();
    const mode = document.querySelector('input[name="mode"]:checked').value;

    if (!formula) {
        showStatus('Please enter a formula', 'error');
        return;
    }

    showLoading(true);
    hideStatus();
    clearProofs();

    try {
        // Préparer les données à envoyer
        const requestData = {
            formula: formula,
            mode: mode
        };

        // Appeler le script CGI
        const response = await fetch(API_URL, {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(requestData)
        });

        if (!response.ok) {
            throw new Error(`HTTP error! status: ${response.status}`);
        }

        const data = await response.json();

        if (data.error) {
            showStatus(`Error: ${data.error}`, 'error');
        } else if (mode === 'decide') {
            // Handle decide mode
            if (data.result === 'provable') {
                showStatus(`✓ Formula is PROVABLE (${data.logic_level})`, 'success');
            } else {
                showStatus(`✗ Formula is NOT PROVABLE`, 'error');
            }
        } else {
            // Handle full proof mode
            if (data.provable) {
                showStatus(`✓ Proof found! (${data.logic_level})`, 'success');
                displayProofs(data.proofs);
            } else {
                showStatus('✗ No proof found', 'error');
            }
        }
    } catch (error) {
        showStatus(`Error: ${error.message}`, 'error');
        console.error('Detailed error:', error);
    } finally {
        showLoading(false);
    }
}

function displayProofs(proofs) {
    const container = document.getElementById('proof-container');
    
    // Order: Sequent, Fitch, Tree
    const order = ['sequent', 'fitch', 'tree'];
    const titles = {
        'sequent': 'Sequent Calculus (G4)',
        'fitch': 'Natural Deduction - Fitch Style',
        'tree': 'Natural Deduction - Tree Style'
    };

    order.forEach(format => {
        if (proofs[format]) {
            const div = document.createElement('div');
            div.className = 'proof-format';
            
            const title = document.createElement('h3');
            title.textContent = titles[format];
            div.appendChild(title);

            const content = document.createElement('div');
            content.className = 'proof-content';
            content.innerHTML = proofs[format];
            div.appendChild(content);

            container.appendChild(div);
        }
    });

    // Trigger MathJax rendering
    if (window.MathJax) {
        MathJax.typesetPromise([container]).catch((err) => {
            console.error('MathJax rendering error:', err);
        });
    }
}

function handleClear() {
    document.getElementById('formula').value = '';
    clearProofs();
    hideStatus();
}

function clearProofs() {
    document.getElementById('proof-container').innerHTML = '';
}

function showStatus(message, type) {
    const status = document.getElementById('status');
    status.textContent = message;
    status.className = `status ${type}`;
}

function hideStatus() {
    const status = document.getElementById('status');
    status.className = 'status';
}

function showLoading(show) {
    document.getElementById('loading').style.display = show ? 'block' : 'none';
    document.getElementById('prove-btn').disabled = show;
}
