(***********************************************************************************
 * Copyright (c) 2022 University of Exeter, UK
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)

section\<open>Line Classification Model (\thy)\<close>

text\<open>
In the
following, we introduce neural networks for (image) classification by using a
simple line classification problem: given a $2 \times 2$ pixel greyscale image,
the neural network should decide if the image contains a horizontal line (e.g.,
\autoref{fig:h_line}), vertical line (e.g., \autoref{fig:v_line}), or no line
(\autoref{fig:n_line}).
\begin{figure}[ht] % <---    
  \begin{subfigure}{0.24\textwidth} 
    \centering
    \includegraphics[width=.35\linewidth]{grid-horizontal}
    \caption{horizontal line}
    \label{fig:h_line}
  \end{subfigure}
\hfill % <--- 
  \begin{subfigure}{0.24\textwidth}
    \centering
      \includegraphics[width=.35\linewidth]{grid-vertical}
      \caption{vertical line}
      \label{fig:v_line}
  \end{subfigure}
\hfill % <---
  \begin{subfigure}{0.24\textwidth}
    \centering
      \includegraphics[width=.35\linewidth]{grid-noline}
      \caption{no line}
      \label{fig:n_line}
  \end{subfigure}
  \hfill % <---
    \begin{subfigure}{0.24\textwidth}
      \centering
      \includegraphics[width=.35\linewidth]{grid-misclassification}
        \caption{misclassification}
        \label{fig:miss_line}
    \end{subfigure}
  \caption{Example input images to our classification problem.}
  \label{fig:grid-net-inputs}
\end{figure}

Traditionally, textbooks (e.g.,~\<^cite>\<open>"aggarwal:neural:2018"\<close>) define a
feedforward neural network as directed weighted acyclic graphs. The nodes are
called \emph{neurons} and the incoming edges are called \emph{inputs}. For a
given neuron $k$ with $m$ inputs $x_{k_0}$ to $x_{k_{m-1}}$, and the respective
weights $w_{k_0}$ to $w_{k_{m-1}}$ the neuron computes the output
\begin{equation}
  \label{weighted-sum-def}
  y_{k}=\varphi \left(\beta \sum_{j=0}^{m} w_{k_j} x_{k_j}\right)
\end{equation}
where $\varphi$ is the \emph{activation function} and $\beta$ the \emph{bias}
for the neuron $k$. The values for the weights and biases are determined during
the training (learning) phase, which we omit due to space reasons. In our work,
we assume that the given neural network is already trained, e.g., using the
widely used machine learning framework
TensorFlow~\<^cite>\<open>"abadi.ea:tensorflow:2015"\<close>.

\autoref{fig:grid-net} illustrates the architecture of our neural network:
The neural network for our example classification problem has four inputs (one for
each pixel of the image), expecting an input value between $0.0$ (white) and
$1.0$ (black).
\begin{figure*}
  \centering
  \includegraphics[width=0.5\textwidth]{grid-nn}
  \caption{Neural network for classifying lines in $2 \times 2$ pixel grey scale images.}
  \label{fig:grid-net}
\end{figure*}
It also has three outputs, one for each possible class (horizontal line,
vertical line, no line). The neurons (nodes) can be naturally categorised into
layers, i.e., the \emph{input layer} consisting out of the input nodes and the
\emph{output layer} consisting out of the output nodes. Moreover, our neural
network has one \emph{hidden layer} with 16 neurons. The input layer and the
hidden layer use a linear activation function (i.e., $\varphi(x) = x$) for all
neurons, and the hidden layer uses the binary step function (i.e., $\varphi(x)=0$
for $x \leq 0$ and $\varphi(x) =1$ otherwise). In our
example, there is an edge between each neuron from the previous layer to the
next layer. This is often called a \emph{dense layer}. Machine learning
approaches using neural networks with one or more hidden layers are called
\emph{deep learning}.

In our example, we used the Python API for
TensorFlow~\<^cite>\<open>"abadi.ea:tensorflow:2015"\<close> to train our neural network. We
obtained neural network that reliably classifies black lines in a given $2
\times 2$ image with 100\% accuracy. While this sounds great, the neural network
is not very resilient to changes to its input values. Consider, for example,
\autoref{fig:miss_line}: a human expert would, very likely, classify this image
as ``no line''. Yet our neural network classifies this as a horizontal line,
even though the right upper pixel is only light grey with a numerical value of 0.05,
much closer to white than to black. Such a misclassification is usually called
an \emph{adversarial example}. If such a network is used in a safety or security
critical applications, e.g., for classifying street signs, such misclassifications
can be life-threatening.

\<close>

(*>*)
theory
  Grid_Layers
  imports
  NN_Layers_List_Main
begin
end 
(*>*)
