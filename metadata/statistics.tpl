<!DOCTYPE public "-//w3c//dtd html 4.01 transitional//en"
		"http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
  <title>Archive of Formal Proofs</title>
  <link rel="stylesheet" type="text/css" href="front.css">
  <link rel="icon" href="images/favicon.ico" type="image/icon">
  <meta http-equiv="Content-Type" content="text/html; charset=utf-8">
</head>
<body>

<table width="100%">
  <tbody>
    <tr>
      <td width="20%" align="center" valign="top">
      <!-- navigation -->
      <!--#include file="nav.html"-->
      </td>
      <td width="80%" valign="top">
      <!-- content -->

<div align="center">
<p>&nbsp;</p>
<h1><font class="first">A</font>rchive of
    <font class="first">F</font>ormal
    <font class="first">P</font>roofs</h1>
<p>&nbsp;</p>


<table width="80%" class="descr">
  <tbody>
    <tr><td>
      <h2>Statistics</h2>

<!--gen-->

<h4>Growth in number of articles:</h4>
<script src="Chart.js"></script>
<div class="chart">
<canvas id="NumberOfArticles" width="400" height="400"></canvas>
</div>
<script>
var ctx = document.getElementById("NumberOfArticles");
var myChart = new Chart(ctx, {
    type: 'bar',
    data: {
        labels: years,
        datasets: [{
            label: 'size of the AFP in # of articles',
            data: no_articles,
            backgroundColor: "rgba(46, 45, 78, 1)"
        }],
    },
    options: {
        responsive: true,
        maintainAspectRatio: true,
        scales: {
            yAxes: [{
                ticks: {
                    beginAtZero:true
                }
            }]
        },
     }
});
</script>

<h4>Growth in lines of code:</h4>
<div class="chart">
<canvas id="NumberOfLoc" width="400" height="400"></canvas>
</div>
<script>
var ctx = document.getElementById("NumberOfLoc");
var myChart = new Chart(ctx, {
    type: 'bar',
    data: {
        labels: years,
        datasets: [{
            label: 'size of the AFP in lines of code',
            data: no_loc,
            backgroundColor: "rgba(101, 99, 136, 1)"
        }],
    },
    options: {
        responsive: true,
        maintainAspectRatio: true,
        scales: {
            yAxes: [{
                ticks: {
                    beginAtZero:true
                }
            }]
        },
     }
});
</script>

<h4>Growth in number of authors:</h4>
<div class="chart">
<canvas id="NumberOfAuthors" width="400" height="400"></canvas>
</div>
<script>
var ctx = document.getElementById("NumberOfAuthors");
var myChart = new Chart(ctx, {
    type: 'bar',
    data: {
        labels: years,
        datasets: [{
            label: 'new authors per year',
            data: no_authors,
            backgroundColor: "rgba(101, 99, 136, 1)"
            },
            {
            label: 'number of authors contributing (cumulative)',
            data: no_authors_series,
            backgroundColor: "rgba(0, 15, 48, 1)"
        }],
    },
    options: {
        responsive: true,
        maintainAspectRatio: true,
        scales: {
            yAxes: [{
                ticks: {
                    beginAtZero:true
                }
            }]
        },
     }
});
</script>

<h4>Size of articles:</h4>
<div style="width: 800px" class="chart">
<canvas id="LocArticles" width="800" height="400"></canvas>
</div>
<script>
var ctx = document.getElementById("LocArticles");
var myChart = new Chart(ctx, {
    type: 'bar',
    data: {
        labels: years_loc_articles,
        datasets: [{
            label: 'loc per article',
            data: loc_articles,
            backgroundColor: "rgba(101, 99, 136, 1)"
            }]
    },
    options: {
        responsive: true,
        maintainAspectRatio: true,
        scales: {
            xAxes: [{
                categoryPercentage: 1,
                barPercentage: 0.9,
                ticks: {
                    autoSkip: false
                }
                }],
            yAxes: [{
                ticks: {
                    beginAtZero:true
                }
            }]
        },
        tooltips: {
            callbacks: {
                title: function(tooltipItem, data) {
                       return all_articles[tooltipItem[0].index];
                       }
            }
        }
     }
});
</script>

    </td></tr>

  </tbody>
</table>

</div>
</td> </tr> </table>
</body>
</html>
