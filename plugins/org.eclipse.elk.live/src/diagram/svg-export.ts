/*
 * SVG export of the rendered diagram: a copy of sprotty's `<svg>` with the viewport transform
 * replaced by a viewBox around the drawing and the diagram stylesheet embedded, so that the file
 * renders like the page (elk-live exports through sprotty's SvgExporter, which needs a server).
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 */
import diagramCss from './diagram.css?raw';

export function exportSvg(container: HTMLElement, dark: boolean, padding = 10): string | null {
  const svgEl = container.querySelector('svg');
  const g = svgEl?.querySelector(':scope > g');
  if (!svgEl || !(g instanceof SVGGraphicsElement)) return null;
  const box = g.getBBox();
  const copy = svgEl.cloneNode(true) as SVGSVGElement;
  const gCopy = copy.querySelector(':scope > g');
  gCopy?.removeAttribute('transform');
  copy.removeAttribute('id');
  copy.removeAttribute('class');
  copy.removeAttribute('style');
  copy.setAttribute('xmlns', 'http://www.w3.org/2000/svg');
  const x = box.x - padding;
  const y = box.y - padding;
  const w = box.width + 2 * padding;
  const h = box.height + 2 * padding;
  copy.setAttribute('viewBox', `${x} ${y} ${w} ${h}`);
  copy.setAttribute('width', String(Math.ceil(w)));
  copy.setAttribute('height', String(Math.ceil(h)));
  if (dark) copy.setAttribute('class', 'elk-dark-mode');
  const style = document.createElementNS('http://www.w3.org/2000/svg', 'style');
  style.textContent = diagramCss.replace(/\/\*[\s\S]*?\*\//g, '').trim()
    + (dark ? '\nsvg.elk-dark-mode { background: #333; }' : '');
  copy.insertBefore(style, copy.firstChild);
  // drop interaction classes
  copy.querySelectorAll('.selected, .mouseover').forEach((el) => el.classList.remove('selected', 'mouseover'));
  return '<?xml version="1.0" encoding="UTF-8"?>\n' + new XMLSerializer().serializeToString(copy);
}

export function download(name: string, text: string, type: string): void {
  const url = URL.createObjectURL(new Blob([text], { type }));
  const a = document.createElement('a');
  a.href = url;
  a.download = name;
  document.body.appendChild(a);
  a.click();
  a.remove();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}
