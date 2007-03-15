/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class ANever extends PNever
{
    private TNevertok _nevertok_;
    private TLBrace _lBrace_;
    private PSequence _sequence_;
    private TRBrace _rBrace_;

    public ANever()
    {
        // Constructor
    }

    public ANever(
        @SuppressWarnings("hiding") TNevertok _nevertok_,
        @SuppressWarnings("hiding") TLBrace _lBrace_,
        @SuppressWarnings("hiding") PSequence _sequence_,
        @SuppressWarnings("hiding") TRBrace _rBrace_)
    {
        // Constructor
        setNevertok(_nevertok_);

        setLBrace(_lBrace_);

        setSequence(_sequence_);

        setRBrace(_rBrace_);

    }

    @Override
    public Object clone()
    {
        return new ANever(
            cloneNode(this._nevertok_),
            cloneNode(this._lBrace_),
            cloneNode(this._sequence_),
            cloneNode(this._rBrace_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseANever(this);
    }

    public TNevertok getNevertok()
    {
        return this._nevertok_;
    }

    public void setNevertok(TNevertok node)
    {
        if(this._nevertok_ != null)
        {
            this._nevertok_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._nevertok_ = node;
    }

    public TLBrace getLBrace()
    {
        return this._lBrace_;
    }

    public void setLBrace(TLBrace node)
    {
        if(this._lBrace_ != null)
        {
            this._lBrace_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._lBrace_ = node;
    }

    public PSequence getSequence()
    {
        return this._sequence_;
    }

    public void setSequence(PSequence node)
    {
        if(this._sequence_ != null)
        {
            this._sequence_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._sequence_ = node;
    }

    public TRBrace getRBrace()
    {
        return this._rBrace_;
    }

    public void setRBrace(TRBrace node)
    {
        if(this._rBrace_ != null)
        {
            this._rBrace_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._rBrace_ = node;
    }

    @Override
    public String toString()
    {
        return ""
            + toString(this._nevertok_)
            + toString(this._lBrace_)
            + toString(this._sequence_)
            + toString(this._rBrace_);
    }

    @Override
    void removeChild(@SuppressWarnings("unused") Node child)
    {
        // Remove child
        if(this._nevertok_ == child)
        {
            this._nevertok_ = null;
            return;
        }

        if(this._lBrace_ == child)
        {
            this._lBrace_ = null;
            return;
        }

        if(this._sequence_ == child)
        {
            this._sequence_ = null;
            return;
        }

        if(this._rBrace_ == child)
        {
            this._rBrace_ = null;
            return;
        }

        throw new RuntimeException("Not a child.");
    }

    @Override
    void replaceChild(@SuppressWarnings("unused") Node oldChild, @SuppressWarnings("unused") Node newChild)
    {
        // Replace child
        if(this._nevertok_ == oldChild)
        {
            setNevertok((TNevertok) newChild);
            return;
        }

        if(this._lBrace_ == oldChild)
        {
            setLBrace((TLBrace) newChild);
            return;
        }

        if(this._sequence_ == oldChild)
        {
            setSequence((PSequence) newChild);
            return;
        }

        if(this._rBrace_ == oldChild)
        {
            setRBrace((TRBrace) newChild);
            return;
        }

        throw new RuntimeException("Not a child.");
    }
}
